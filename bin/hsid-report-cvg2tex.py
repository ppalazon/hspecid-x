#!/usr/bin/env python3
import sys
import os
import xml.etree.ElementTree as ET

def escape_latex(text):
    return text.replace("_", "\\_")

def texify(text):
    return f"\\texttt{{{escape_latex(text)}}}"

def fmt_percent(value):
    try:
        return f"{float(value):.2f}"
    except:
        return value

def get_activations(node):
    """Suma <metric> de los bins dentro de <bins> (ignora el bin de cabecera)."""
    total = 0
    bins_node = node.find("bins")
    if bins_node is not None:
        for b in bins_node.findall("bin"):
            m = b.findtext("metric")
            if m is not None:
                try:
                    total += int(float(m))
                except:
                    pass
    return total

def main():
    if len(sys.argv) != 2:
        print(f"Uso: {sys.argv[0]} <nombre_modulo>")
        sys.exit(1)

    module = sys.argv[1]
    xml_file = os.path.join("reports", module, "cvg_details.xml")
    tex_file = os.path.join("reports", module, "cvg_table.tex")

    if not os.path.isfile(xml_file):
        print(f"Error: no existe el fichero {xml_file}")
        sys.exit(1)

    tree = ET.parse(xml_file)
    root = tree.getroot()

    cvg = root.find(".//functional_coverage_report/cvgreport/covertype/coverinstance")
    if cvg is None:
        print("Error: no se encontró sección <functional_coverage_report>")
        sys.exit(1)

    with open(tex_file, "w") as f:
        f.write("\\begin{table}[H]\n")
        f.write("\\centering\n")

        # ---------------- Tabla Coverpoints ----------------
        f.write("\\begin{tabular}{lrrrr}\n")
        f.write("\\textbf{Coverpoint} & \\textbf{Activaciones} & "
                "\\textbf{Cubiertos} & \\textbf{Perdidos} & \\textbf{Porcentaje} \\\\\n")
        f.write("\\hline\n")

        for cp in cvg.findall("coverpoint"):
            name = cp.find("./bin/name").text if cp.find("./bin/name") is not None else "?"
            covered = cp.findtext("coveredbins", "0")
            missing = cp.findtext("missingbins", "0")
            percent = fmt_percent(cp.findtext("percenthit", "0.00"))
            activations = get_activations(cp)

            f.write(f"{texify(name)} & {activations} & {covered} & {missing} & {percent} \\\\\n")

        f.write("\\end{tabular}\n")
        f.write("\\vspace{0.5cm}\n")

        # ---------------- Tabla Crosses ----------------
        f.write("\\begin{tabular}{l l r r r r}\n")
        f.write("\\textbf{Cross} & \\textbf{Coverpoints} & "
                "\\textbf{Activaciones} & \\textbf{Covered} & \\textbf{Missing} & \\textbf{Percent} \\\\\n")
        f.write("\\hline\n")

        for cross in cvg.findall("cross"):
            name = cross.find("./bin/name").text if cross.find("./bin/name") is not None else "?"
            covered = cross.findtext("coveredbins", "0")
            missing = cross.findtext("missingbins", "0")
            percent = fmt_percent(cross.findtext("percenthit", "0.00"))
            activations = get_activations(cross)

            cps = [texify(cp.text) for cp in cross.findall("cross_coverpoints/cross_coverpoint")]
            cps_str = ", ".join(cps)

            f.write(f"{texify(name)} & {cps_str} & {activations} & {covered} & {missing} & {percent} \\\\\n")

        f.write("\\end{tabular}\n")

        # ---------------- Caption y label ----------------
        module_latex = escape_latex(module)
        f.write(f"\\caption{{Cobertura de covergroups para \\texttt{{{module_latex}}}}}\n")
        f.write(f"\\label{{tab:{module}_cvg}}\n")
        f.write("\\end{table}\n")

    print(f"Tabla LaTeX generada en {tex_file}")

if __name__ == "__main__":
    main()
