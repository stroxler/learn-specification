#!/usr/bin/env python3
"""Convert an Alloy solution JSON trace into TLA constant assignments.

Usage:
  python3 scripts/alloy_trace_to_tla_constants.py <solution.json> <out.cfg.inc>
"""

import json
import re
import sys
from pathlib import Path


def parse_int(atom: str) -> int:
    return int(atom)


def node_sort_key(atom: str):
    m = re.match(r"Node\$(\d+)$", atom)
    if m:
        return (0, int(m.group(1)))
    return (1, atom)


def tla_set(items):
    if not items:
        return "{}"
    return "{" + ", ".join(f'"{x}"' for x in items) + "}"


def tla_func(mapping: dict[str, set[str]]) -> str:
    lines = ["["]
    keys = sorted(mapping.keys())
    for i, k in enumerate(keys):
        suffix = "," if i < len(keys) - 1 else ""
        lines.append(f'  "{k}" |-> {tla_set(sorted(mapping[k]))}{suffix}')
    lines.append("]")
    return "\n".join(lines)


def tla_step_func(step_map: dict[int, dict[str, set[str]]]) -> str:
    lines = ["["]
    keys = sorted(step_map.keys())
    for i, k in enumerate(keys):
        suffix = "," if i < len(keys) - 1 else ""
        nested = tla_func(step_map[k]).replace("\n", "\n    ")
        lines.append(f"  {k} |-> {nested}{suffix}")
    lines.append("]")
    return "\n".join(lines)


def main() -> int:
    if len(sys.argv) != 3:
        print("Usage: alloy_trace_to_tla_constants.py <solution.json> <out.cfg.inc>")
        return 2

    inp = Path(sys.argv[1])
    out = Path(sys.argv[2])

    data = json.loads(inp.read_text())
    if not data.get("instances"):
        print("ERROR: no instances in Alloy solution JSON")
        return 1

    values = data["instances"][0]["values"]

    node_atom_set = {k for k in values if k.startswith("Node$")}
    for src, dst in values.get("FullGraph$0", {}).get("edges", []):
        if isinstance(src, str) and src.startswith("Node$"):
            node_atom_set.add(src)
        if isinstance(dst, str) and dst.startswith("Node$"):
            node_atom_set.add(dst)
    for k in [kk for kk in values if kk.startswith("Step$")]:
        for src, dst in values[k].get("edges", []):
            if isinstance(src, str) and src.startswith("Node$"):
                node_atom_set.add(src)
            if isinstance(dst, str) and dst.startswith("Node$"):
                node_atom_set.add(dst)

    node_atoms = sorted(node_atom_set, key=node_sort_key)
    if not node_atoms:
        print("ERROR: no Node atoms found")
        return 1

    aliases = {atom: f"n{i}" for i, atom in enumerate(node_atoms)}
    nodes = [aliases[a] for a in node_atoms]

    fg = values.get("FullGraph$0", {})
    full_edges = fg.get("edges", [])
    full_graph = {n: set() for n in nodes}
    for src, dst in full_edges:
        full_graph[aliases[src]].add(aliases[dst])

    params = values.get("Params$0", {})
    step_count = None
    if "step_count" in params and params["step_count"]:
        step_count = parse_int(params["step_count"][0][0])

    step_atoms = sorted([k for k in values if k.startswith("Step$")], key=node_sort_key)
    step_map: dict[int, dict[str, set[str]]] = {}
    for s in step_atoms:
        val = values[s]
        idx = parse_int(val["idx"][0][0])
        if idx in step_map:
            print(f"ERROR: duplicate step index {idx}")
            return 1
        g = {n: set() for n in nodes}
        for src, dst in val.get("edges", []):
            g[aliases[src]].add(aliases[dst])
        step_map[idx] = g

    if step_count is None:
        step_count = len(step_map)

    mapping_lines = ["\\* Node mapping (alias -> Alloy atom):"]
    for atom in node_atoms:
        mapping_lines.append(f"\\* {aliases[atom]} = {atom}")

    out_lines = []
    out_lines.extend(mapping_lines)
    out_lines.append(f"CONSTANT Nodes = {tla_set(nodes)}")
    out_lines.append(f"CONSTANT StepCount = {step_count}")
    out_lines.append("CONSTANT FullGraph = " + tla_func(full_graph))
    out_lines.append("CONSTANT DynamicSteps = " + tla_step_func(step_map))
    out_lines.append("")

    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text("\n".join(out_lines))
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
