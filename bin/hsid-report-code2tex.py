#!/usr/bin/env python3
import sys
import os
import xml.etree.ElementTree as ET

def get_metric(element, name):
    """Extrae active, hits y percent de un nodo y devuelve fila de tabla."""
    if element is None:
        return None
    active = element.get("active", "0")
    hits   = element.get("hits", "0")
    percent= element.get("percent", "0.00")
    return (name, active, hits, percent)

def main():
    if len(sys.argv) != 2:
        print(f"Uso: {sys.argv[0]} <nombre_modulo>")
        sys.exit(1)

    module = sys.argv[1]
    xml_file = os.path.join("reports", module, "dut_code.xml")
    tex_file = os.path.join("reports", module, "dut_code_table.tex")

    if not os.path.isfile(xml_file):
        print(f"Error: no existe el fichero {xml_file}")
        sys.exit(1)

    tree = ET.parse(xml_file)
    root = tree.getroot()
    inst = root.find(".//instanceData")
    if inst is None:
        print("Error: no se encontró <instanceData> en el XML")
        sys.exit(1)

    rows = []

    # Orden fijo para las métricas
    rows.append(get_metric(inst.find("branches"), "Branch coverage"))
    for ifnode in inst.findall("if"):
        hasElse = ifnode.get("hasElse")
        if hasElse == "1":
            rows.append(get_metric(ifnode, "If-Else coverage"))
        elif hasElse == "0":
            rows.append(get_metric(ifnode, "If coverage (sin else)"))
    rows.append(get_metric(inst.find("case"), "Case coverage"))
    rows.append(get_metric(inst.find("fec_conditions"), "Condition coverage"))
    rows.append(get_metric(inst.find("fec_expressions"), "Expression coverage"))
    rows.append(get_metric(inst.find("statements"), "Statement coverage"))
    rows.append(get_metric(inst.find("toggleSummary"), "Toggle coverage"))

    rows = [r for r in rows if r is not None]

    # Escapar guiones bajos en el caption
    module_latex = module.replace("_", "\\_")

    # Generar tabla LaTeX
    with open(tex_file, "w") as f:
        f.write("\\begin{table}[H]\n")
        f.write("\\centering\n")
        f.write("\\begin{tabular}{lrrr}\n")
        f.write("\\textbf{Metric} & \\textbf{Active} & \\textbf{Hits} & \\textbf{Percent} \\\\\n")
        f.write("\\hline\n")
        for name, active, hits, percent in rows:
            f.write(f"{name} & {active} & {hits} & {percent} \\\\\n")
        f.write("\\end{tabular}\n")
        f.write(f"\\caption{{Cobertura de código para \\texttt{{{module_latex}}}}}\n")
        f.write(f"\\label{{tab:{module}_code_cov}}\n")
        f.write("\\end{table}\n")

    print(f"Tabla LaTeX generada en {tex_file}")

if __name__ == "__main__":
    main()