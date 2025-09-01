#!/usr/bin/env python3
import sys
import os
import re
import xml.etree.ElementTree as ET

def clean_xml(xml_file):
    """Crea una versión corregida del XML quitando las líneas mal formadas."""
    cleaned_file = xml_file + ".cleaned"
    with open(xml_file, "r") as fin, open(cleaned_file, "w") as fout:
        for line in fin:
            # Si detecta un <togenum ...<tog .../> lo elimina
            if re.search(r"<togenum[^>]*<tog", line):
                continue
            fout.write(line)
    return cleaned_file

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

    # Preprocesar XML para quitar líneas rotas
    cleaned_xml = clean_xml(xml_file)

    # Parsear el XML ya limpio
    tree = ET.parse(cleaned_xml)
    root = tree.getroot()
    inst = root.find(".//instanceData")
    if inst is None:
        print("Error: no se encontró <instanceData> en el XML")
        sys.exit(1)

    rows = []

    # Orden fijo para las métricas (sin if/if-else)
    rows.append(get_metric(inst.find("branches"), "Branch coverage"))
    rows.append(get_metric(inst.find("case"), "Case coverage"))
    rows.append(get_metric(inst.find("fec_conditions"), "Condition coverage"))
    rows.append(get_metric(inst.find("fec_expressions"), "Expression coverage"))
    rows.append(get_metric(inst.find("statements"), "Statement coverage"))
    rows.append(get_metric(inst.find("toggleSummary"), "Toggle coverage"))
    rows.append(get_metric(inst.find("transitions"), "Transition coverage"))

    rows = [r for r in rows if r is not None]

    # Escapar guiones bajos en el caption
    module_latex = module.replace("_", "\\_")

    # Generar tabla LaTeX
    with open(tex_file, "w") as f:
        f.write("\\begin{table}[H]\n")
        f.write("\\centering\n")
        f.write("\\begin{tabular}{lrrr}\n")
        f.write("\\textbf{Métrica} & \\textbf{Activos} & \\textbf{Aciertos} & \\textbf{Porcentaje} \\\\\n")
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