set top "hsid_divider_tb"
run -all

file mkdir report
coverage save -testname $top report/$top.ucdb

# Reporte “resumen” global
vcover report -summary -assert -cvg -code bcestf \
  -output report/summary.txt report/$top.ucdb

# Reporte SVA detallado
vcover report -details -assert -concurrent -lang sva \
  -output report/sva_details.txt report/$top.ucdb

# Reporte SVA detallado (xml)
vcover report -details -xml -assert -concurrent -lang sva \
  -output report/sva_details.xml report/$top.ucdb

# Reporte CVG detallado
vcover report -details -cvg \
  -output report/cvg_details.txt report/$top.ucdb

# Reporte CVG detallado (xml)
vcover report -xml -details -cvg \
  -output report/cvg_details.xml report/$top.ucdb

# Reporte code (por instancia del DUT)
vcover report -details -instance=/$top/dut -code bcestf \
  -output report/dut_code.txt report/$top.ucdb

# Reporte code (por instancia del DUT) (xml)
vcover report -details -xml -instance=/$top/dut -code bcestf \
  -output report/dut_code.xml report/$top.ucdb

# Html report
vcover report -html -details -assert -cvg -code bcestf -output report/html report/$top.ucdb

quit -f