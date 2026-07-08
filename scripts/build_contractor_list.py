#!/usr/bin/env python3
"""Build a password-encrypted contractor lead list page (leads.html).

Pulls the NJ Division of Consumer Affairs public licensee rosters (free bulk
download published at https://app.box.com/v/DCAStandardFiles, linked from
https://www.njconsumeraffairs.gov/requestlist), filters to active:
  - Home Improvement Contractors (business registrations; includes roofers/GCs)
  - Electrical Contractors (Electrical Business Permit holders only)
  - Master Plumbers (individual license; NJ plumbing businesses operate under one)
within RADIUS_MILES of the property, then writes:
  - .data/leads.csv           (cleartext CSV, NOT committed — .data/ is gitignored)
  - leads.html                (AES-256-GCM encrypted page; committed & served)

Distance is measured from each licensee's zip-code centroid (Census 2023 ZCTA
gazetteer) to the property coordinates, so it is approximate to a few miles.

Usage:
  python3 scripts/build_contractor_list.py --password 'SECRET' [--dry]

Idempotent: downloads are cached in .data/; re-runs regenerate outputs from
the cached data. Use --refresh to force fresh roster downloads.
"""

import argparse
import base64
import csv
import gzip
import io
import json
import math
import os
import re
import sys
import urllib.request
import zipfile

from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
from cryptography.hazmat.primitives import hashes

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DATA_DIR = os.path.join(ROOT, ".data")

PROPERTY_ADDRESS = "237 Prospect Plains Rd, Monroe Township, NJ 08831"
PROPERTY_LAT = 40.324418968149   # Census geocoder result for the address above
PROPERTY_LON = -74.471899049888
RADIUS_MILES = 50.0

BOX_FOLDER_URL = "https://app.box.com/v/DCAStandardFiles"
BOX_DOWNLOAD = "https://app.box.com/index.php?rm=box_download_shared_file&shared_name={shared}&file_id=f_{fid}"
GAZETTEER_URL = "https://www2.census.gov/geo/docs/maps-data/data/gazetteer/2023_Gazetteer/2023_Gaz_zcta_national.zip"
ZCTA_COUNTY_URL = "https://www2.census.gov/geo/docs/maps-data/data/rel2020/zcta520/tab20_zcta520_county20_natl.txt"

PBKDF2_ITERATIONS = 310_000

# (roster file prefix, cached filename)
ROSTERS = [
    ("Standard Facilities active statuses", "dca_facilities_active.txt"),
    ("Standard Individuals active statuses", "dca_individuals_active.txt"),
]

# Column indexes in the '%'-delimited DCA standard files (facilities have 25
# columns ending in email, phone; individuals have 24, ending in email).
COL_PROFESSION, COL_LICTYPE, COL_LICNO, COL_STATUS = 0, 1, 2, 3
COL_EXPIRES = 5
COL_FIRST, COL_MIDDLE, COL_LAST = 9, 10, 11
COL_ORGNAME, COL_ADDR1, COL_ADDR2 = 13, 14, 15
COL_CITY, COL_STATE, COL_ZIP, COL_COUNTY = 18, 19, 20, 21
COL_EMAIL = 23
COL_PHONE = 24  # facilities only


def fetch(url, dest, label):
    if os.path.exists(dest):
        print(f"  cached: {label} ({os.path.getsize(dest):,} bytes)")
        return
    print(f"  downloading: {label} ...")
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req) as r, open(dest, "wb") as f:
        f.write(r.read())
    print(f"  saved: {dest} ({os.path.getsize(dest):,} bytes)")


def download_rosters(refresh=False):
    os.makedirs(DATA_DIR, exist_ok=True)
    paths = {}
    missing = []
    for prefix, fname in ROSTERS:
        dest = os.path.join(DATA_DIR, fname)
        paths[prefix] = dest
        if refresh and os.path.exists(dest):
            os.remove(dest)
        if not os.path.exists(dest):
            missing.append((prefix, dest))
    if not missing:
        for prefix, fname in ROSTERS:
            print(f"  cached: {fname}")
        return paths

    # Box file IDs rotate when DCA re-uploads each month, so resolve them
    # from the shared-folder page every time we need a fresh download.
    req = urllib.request.Request(BOX_FOLDER_URL, headers={"User-Agent": "Mozilla/5.0"})
    html = urllib.request.urlopen(req).read().decode("utf-8", "replace")
    start = html.find("Box.postStreamData = ")
    if start < 0:
        sys.exit("Could not parse Box folder page (postStreamData not found)")
    obj, _ = json.JSONDecoder().raw_decode(html[start + len("Box.postStreamData = "):])
    shared = obj["/app-api/enduserapp/shared-item"]["sharedName"]
    items = obj["/app-api/enduserapp/shared-folder"]["items"]
    for prefix, dest in missing:
        match = next((it for it in items if it.get("name", "").startswith(prefix)), None)
        if not match:
            sys.exit(f"Roster starting with {prefix!r} not found in Box folder")
        fetch(BOX_DOWNLOAD.format(shared=shared, fid=match["id"]), dest, match["name"])
    return paths


def load_zip_centroids():
    zpath = os.path.join(DATA_DIR, "gaz_zcta.zip")
    fetch(GAZETTEER_URL, zpath, "Census ZCTA gazetteer")
    centroids = {}
    with zipfile.ZipFile(zpath) as z:
        with z.open(z.namelist()[0]) as f:
            next(f)
            for raw in f:
                parts = raw.decode("utf-8", "replace").split("\t")
                if len(parts) >= 7:
                    centroids[parts[0].strip()] = (float(parts[5]), float(parts[6]))
    return centroids


def load_zip_counties():
    """zip5 -> county name, picking the county with the largest land overlap.

    The DCA roster's own county column is unreliable free text (typos, stray
    addresses), so county is derived from the zip code instead.
    """
    path = os.path.join(DATA_DIR, "zcta_county.txt")
    fetch(ZCTA_COUNTY_URL, path, "Census ZCTA-to-county relationships")
    best = {}
    with open(path, encoding="utf-8-sig") as f:
        header = f.readline().rstrip("\n").split("|")
        iz, ic, ia = (header.index(c) for c in
                      ("GEOID_ZCTA5_20", "NAMELSAD_COUNTY_20", "AREALAND_PART"))
        for line in f:
            p = line.rstrip("\n").split("|")
            zip5, county = p[iz], p[ic].replace(" County", "")
            if not zip5 or not county:
                continue
            area = int(p[ia] or 0)
            if area > best.get(zip5, ("", -1))[1]:
                best[zip5] = (county, area)
    return {z: c for z, (c, _) in best.items()}


def haversine_miles(lat1, lon1, lat2, lon2):
    r = 3958.8
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp, dl = math.radians(lat2 - lat1), math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * r * math.asin(math.sqrt(a))


def fmt_phone(digits):
    d = re.sub(r"\D", "", digits or "")
    if len(d) == 10:
        return f"({d[:3]}) {d[3:6]}-{d[6:]}"
    return digits or ""


def wanted(vals):
    """Return trade label if this roster row is a target record, else None."""
    prof, lictype, status = vals[COL_PROFESSION], vals[COL_LICTYPE].strip(), vals[COL_STATUS]
    if status != "Active":
        return None
    if prof == "Home Improvement Contractors":
        return "Home Improvement / GC"
    if prof == "Electrical Contractors" and lictype == "Electrical Business Permit":
        return "Electrician"
    if prof == "Master Plumbers" and lictype == "Master Plumber":
        return "Plumber"
    return None


def parse_rosters(paths, centroids, zip_counties):
    rows, seen = [], set()
    stats = {"total": 0, "matched": 0, "no_zip_centroid": 0, "outside_radius": 0}
    for path in paths.values():
        with open(path, encoding="cp1252") as f:
            next(f)
            for line in f:
                vals = line.rstrip("\n").split("%")
                if len(vals) < 24:
                    continue
                stats["total"] += 1
                trade = wanted(vals)
                if not trade:
                    continue
                licno = vals[COL_LICNO].strip()
                if licno in seen:
                    continue
                zip5 = re.sub(r"\D", "", vals[COL_ZIP])[:5]
                cent = centroids.get(zip5)
                if not cent:
                    stats["no_zip_centroid"] += 1
                    continue
                miles = haversine_miles(PROPERTY_LAT, PROPERTY_LON, cent[0], cent[1])
                if miles > RADIUS_MILES:
                    stats["outside_radius"] += 1
                    continue
                seen.add(licno)
                stats["matched"] += 1
                owner = " ".join(x for x in (vals[COL_FIRST].strip(), vals[COL_LAST].strip()) if x)
                addr = ", ".join(x for x in (vals[COL_ADDR1].strip(), vals[COL_ADDR2].strip()) if x)
                phone = vals[COL_PHONE] if len(vals) > COL_PHONE else ""
                rows.append({
                    "trade": trade,
                    "business": vals[COL_ORGNAME].strip() or owner,
                    "owner": owner,
                    "address": addr,
                    "city": vals[COL_CITY].strip(),
                    "state": vals[COL_STATE].strip(),
                    "zip": zip5,
                    "county": zip_counties.get(zip5, vals[COL_COUNTY].strip().title()),
                    "phone": fmt_phone(phone),
                    "email": vals[COL_EMAIL].strip().lower(),
                    "license": licno,
                    "expires": vals[COL_EXPIRES].strip(),
                    "miles": round(miles, 1),
                })
    rows.sort(key=lambda r: r["miles"])
    return rows, stats


def write_csv(rows, dest):
    cols = ["trade", "business", "owner", "address", "city", "state", "zip",
            "county", "phone", "email", "license", "expires", "miles"]
    with open(dest, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=cols)
        w.writeheader()
        w.writerows(rows)


def encrypt_payload(rows, password, generated_on):
    payload = {"generated": generated_on, "source": "NJ Division of Consumer Affairs public licensee rosters",
               "radius_miles": RADIUS_MILES, "center": PROPERTY_ADDRESS, "rows": rows}
    plaintext = gzip.compress(json.dumps(payload, separators=(",", ":")).encode())
    salt, nonce = os.urandom(16), os.urandom(12)
    kdf = PBKDF2HMAC(algorithm=hashes.SHA256(), length=32, salt=salt, iterations=PBKDF2_ITERATIONS)
    key = kdf.derive(password.encode())
    ct = AESGCM(key).encrypt(nonce, plaintext, None)
    return (base64.b64encode(salt).decode(), base64.b64encode(nonce).decode(),
            base64.b64encode(ct).decode())


def build_page(salt_b64, nonce_b64, ct_b64, template_path, dest):
    with open(template_path) as f:
        page = f.read()
    page = (page.replace("__SALT__", salt_b64)
                .replace("__NONCE__", nonce_b64)
                .replace("__ITERATIONS__", str(PBKDF2_ITERATIONS))
                .replace("__CIPHERTEXT__", ct_b64))
    with open(dest, "w") as f:
        f.write(page)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--password", help="password for the encrypted page (or env LEADS_PASSWORD)")
    ap.add_argument("--generated-on", required=True, help="date stamp shown on the page, e.g. 2026-07-07")
    ap.add_argument("--dry", action="store_true", help="report counts; write nothing")
    ap.add_argument("--refresh", action="store_true", help="re-download rosters even if cached")
    args = ap.parse_args()

    password = args.password or os.environ.get("LEADS_PASSWORD")
    if not password and not args.dry:
        sys.exit("Provide --password or set LEADS_PASSWORD (never hardcode it — this repo is public)")

    print(f"Scope: active NJ HIC / electrical / master-plumber licensees within "
          f"{RADIUS_MILES:.0f} mi of {PROPERTY_ADDRESS}")
    print("Fetching source data:")
    paths = download_rosters(refresh=args.refresh)
    centroids = load_zip_centroids()
    zip_counties = load_zip_counties()

    rows, stats = parse_rosters(paths, centroids, zip_counties)
    by_trade = {}
    for r in rows:
        by_trade[r["trade"]] = by_trade.get(r["trade"], 0) + 1
    print(f"\nRoster rows scanned: {stats['total']:,}")
    print(f"In-radius leads:     {stats['matched']:,} "
          f"(excluded: {stats['outside_radius']:,} outside radius, "
          f"{stats['no_zip_centroid']:,} bad/unknown zip)")
    for t, n in sorted(by_trade.items()):
        print(f"  {t}: {n:,}")
    with_phone = sum(1 for r in rows if r["phone"])
    with_email = sum(1 for r in rows if r["email"])
    print(f"  with phone: {with_phone:,} ({with_phone/len(rows):.0%})  "
          f"with email: {with_email:,} ({with_email/len(rows):.0%})")

    if args.dry:
        print("\n--dry: no files written")
        return

    csv_dest = os.path.join(DATA_DIR, "leads.csv")
    write_csv(rows, csv_dest)
    print(f"\nWrote {csv_dest} ({os.path.getsize(csv_dest):,} bytes) — NOT committed (gitignored)")

    salt, nonce, ct = encrypt_payload(rows, password, args.generated_on)
    dest = os.path.join(ROOT, "leads.html")
    build_page(salt, nonce, ct, os.path.join(ROOT, "scripts", "leads_template.html"), dest)
    print(f"Wrote {dest} ({os.path.getsize(dest):,} bytes) — AES-256-GCM encrypted, "
          f"PBKDF2 {PBKDF2_ITERATIONS:,} iterations")


if __name__ == "__main__":
    main()
