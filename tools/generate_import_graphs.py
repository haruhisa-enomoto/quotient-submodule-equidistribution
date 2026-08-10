#!/usr/bin/env python3
"""Generate project-only interactive import graphs from Lean import lines."""

from __future__ import annotations

from html import escape
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "website" / "import-graphs"
TARGETS = {
    "main-theorem.html": ("Main theorem", "OpConjecture.RepresentationTheory.MainTheoremEndpoint"),
    "first-last-four.html": ("First and last four", "OpConjecture.RepresentationTheory.FirstLastFourEndpoint"),
    "nakayama.html": ("Nakayama case", "OpConjecture.RepresentationTheory.NakayamaAlgebraProductFormula"),
    "radical-square-zero.html": ("Radical-square-zero case", "OpConjecture.RadicalSquareZero.SeparatedDirectedInterface"),
    "representation-directed.html": ("Representation-directed case", "OpConjecture.RepresentationDirected.AlgebraEndpoint"),
    "generator-minimal.html": ("Generator-minimal dictionary", "OpConjecture.RepresentationTheory.IntrinsicNormalModules"),
}
IMPORT = re.compile(r"(?m)^\s*import\s+([^\s]+)")


def module_map() -> dict[str, Path]:
    result = {"OpConjecture": ROOT / "OpConjecture.lean", "MainResults": ROOT / "MainResults.lean"}
    for path in (ROOT / "OpConjecture").rglob("*.lean"):
        result[".".join(path.relative_to(ROOT).with_suffix("").parts)] = path
    return result


def closure(target: str, modules: dict[str, Path]) -> tuple[set[str], set[tuple[str, str]]]:
    seen: set[str] = set()
    edges: set[tuple[str, str]] = set()
    pending = [target]
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        path = modules[module]
        for imported in IMPORT.findall(path.read_text(encoding="utf-8")):
            if imported not in modules:
                continue
            edges.add((imported, module))
            if imported not in seen:
                pending.append(imported)
    return seen, edges


def color(module: str, target: str) -> str:
    if module == target:
        return "#9c5b27"
    if ".Combinatorics." in module or module.startswith("OpConjecture.Combinatorics"):
        return "#7667a8"
    if ".RepresentationDirected." in module:
        return "#2f6fa3"
    if ".RadicalSquareZero." in module:
        return "#b04d65"
    if ".Foundation." in module:
        return "#718078"
    return "#087d78"


def render(title: str, target: str, nodes: set[str], edges: set[tuple[str, str]]) -> str:
    node_data = [
        {"id": name, "label": name.rsplit(".", 1)[-1], "title": name, "color": color(name, target)}
        for name in sorted(nodes)
    ]
    edge_data = [{"from": source, "to": destination} for source, destination in sorted(edges)]
    module_list = "\n".join(f"<li><code>{escape(name)}</code></li>" for name in sorted(nodes))
    return f"""<!doctype html>
<html lang=\"en\">
<head>
  <meta charset=\"utf-8\">
  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">
  <title>{escape(title)} · import graph</title>
  <script src=\"https://unpkg.com/vis-network@9.1.9/standalone/umd/vis-network.min.js\"></script>
  <style>
    :root {{ font-family: Inter, system-ui, sans-serif; color: #172126; background: #f7f6f1; }}
    body {{ margin: 0; }} header {{ padding: 1rem 1.3rem; border-bottom: 1px solid #d7dfdd; }}
    h1 {{ font: 500 1.55rem Georgia, serif; margin: 0 0 .25rem; }} p {{ margin: .2rem 0; color: #53656d; }}
    a {{ color: #075854; }} #graph {{ width: 100%; height: 78vh; background: white; border-bottom: 1px solid #d7dfdd; }}
    details {{ margin: 1rem 1.3rem 2rem; }} code {{ font-family: ui-monospace, monospace; }}
    li {{ margin: .2rem 0; }}
  </style>
</head>
<body>
  <header><h1>{escape(title)}</h1><p>Project-only transitive import closure of <code>{escape(target)}</code>: {len(nodes)} modules, {len(edges)} direct import edges. Drag to pan; scroll to zoom. <a href=\"../architecture.html\">Back to code map</a>.</p></header>
  <div id=\"graph\" role=\"img\" aria-label=\"Interactive Lean module import graph\"></div>
  <details><summary>Accessible module list</summary><ol>{module_list}</ol></details>
  <script>
    const nodes = new vis.DataSet({json.dumps(node_data, ensure_ascii=False)});
    const edges = new vis.DataSet({json.dumps(edge_data, ensure_ascii=False)});
    const options = {{
      layout: {{ hierarchical: {{ enabled: true, direction: 'DU', sortMethod: 'directed', levelSeparation: 110, nodeSpacing: 105 }} }},
      physics: false,
      nodes: {{ shape: 'box', margin: 8, font: {{ size: 12, color: '#ffffff' }}, borderWidth: 0 }},
      edges: {{ arrows: {{ to: {{ enabled: true, scaleFactor: .45 }} }}, color: '#aab8b5', width: .7, smooth: {{ type: 'cubicBezier' }} }},
      interaction: {{ hover: true, navigationButtons: true, keyboard: true }}
    }};
    new vis.Network(document.getElementById('graph'), {{ nodes, edges }}, options);
  </script>
</body>
</html>
"""


def main() -> None:
    modules = module_map()
    OUTPUT.mkdir(parents=True, exist_ok=True)
    for file_name, (title, target) in TARGETS.items():
        nodes, edges = closure(target, modules)
        (OUTPUT / file_name).write_text(render(title, target, nodes, edges), encoding="utf-8")
        print(f"generated {file_name}: {len(nodes)} modules, {len(edges)} edges")


if __name__ == "__main__":
    main()

