# Print the design point "<gain> <tube radius>" chosen by the selection rule from the campaign
# records of a directory, or nothing when no candidate qualifies. Usage: uv run python design_point.py <outdir>
import sys
from pathlib import Path

from bounds import bounds, candidates, choose, load

out = Path(sys.argv[1])
table = {f"{w}-{d}": bounds(load(out, f"campaign-{w}-{d}")) for w, d in candidates if load(out, f"campaign-{w}-{d}")}
c = choose(table)
if c:
    print(*c)
