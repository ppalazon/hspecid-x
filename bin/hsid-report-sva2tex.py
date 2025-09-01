#!/usr/bin/env python3
import sys
import os
import xml.etree.ElementTree as ET

def latex_escape(s: str) -> str:
    """Escapa caracteres especiales para LaTeX."""
    replacements = {
        "_": "\\_",
        "%": "\\%",
        "&": "\\&",
        "#": "\\#",
        "$": "\\$",
        "{": "\\{",
        "}": "\\}",
    }
    for k, v in replacements.items():
        s = s.replace(k, v)
    return s

def main():
    if len(sys.argv) != 2:
        print(f"Uso: {sys.argv[0]} <nombre_modulo>")
        sys.exit(1)

    module = sys.argv[1]
    xml_file = os.path.join("reports", module, "sva_details.xml")
    tex_file = os.path.join("reports", module, "sva_details_table.tex")

    if not os.path.isfile(xml_file):
        print(f"Error: no existe el fichero {xml_file}")
        sys.exit(1)

    tree = ET.parse(xml_file)
    root = tree.getroot()

    asrt_report = root.find(".//asrtReport")
    if asrt_report is None:
        print("Error: no se encontró <asrtReport> en el XML")
        sys.exit(1)

    module4ltx = latex_escape(module)

    # Extraer resumen (lo dejamos por si quieres mostrarlo al final)
    summary = asrt_report.find("assertion_successes")
    summary_text = ""
    if summary is not None:
        active = summary.get("active", "0")
        hits   = summary.get("hits", "0")
        percent = summary.get("percent", "0.00")
        summary_text = f"\\multicolumn{{4}}{{c}}{{\\textbf{{Resumen: {hits}/{active} aserciones cubiertas ({percent}\\%)}}}} \\\\"

    with open(tex_file, "w") as f:
        f.write("\\begin{table}[H]\n")
        f.write("\\centering\n")
        f.write("\\begin{tabular}{l|l|rr}\n")
        f.write("\\textbf{Fichero} & \\textbf{Propiedad} & \\textbf{Fallos} & \\textbf{Pases} \\\\\n")
        f.write("\\hline\n")

        for a in asrt_report.findall("asrt"):
            passes = int(a.findtext("passcount", "0"))

            # 👇 Filtramos: solo incluir si passes == 0
            if passes != 0:
                continue

            full_name = a.findtext("asrtname", "")
            name = full_name.split("/")[-1] if full_name else "?"

            if name.startswith("assert__"):
                name = name[len("assert__"):]

            name = latex_escape(name)
            name = f"\\texttt{{{name}}}"

            failures = a.findtext("failcount", "0")

            source   = a.findtext("source", "")
            filename = os.path.basename(source.split("(")[0]) if source else "?"
            filename = latex_escape(filename)
            filename = f"\\texttt{{{filename}}}"

            f.write(f"{filename} & {name} & {failures} & {passes} \\\\\n")

        if summary_text:
            f.write("\\hline\n")
            f.write(summary_text + "\n")

        f.write("\\end{tabular}\n")
        f.write(f"\\caption{{Cobertura SVA no activadas y resumen para \\texttt{{{module4ltx}}}}}\n")
        f.write(f"\\label{{tab:{module}_sva_details}}\n")
        f.write("\\end{table}\n")

    print(f"Tabla LaTeX generada en {tex_file}")

if __name__ == "__main__":
    main()
