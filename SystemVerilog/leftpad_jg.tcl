# jg -fpv lefpad_jg.tcl

analyze -sv09 leftpad.sv

# Elaborate design and properties
elaborate -disable_auto_bbox -top leftpad

# Set up Clocks and Resets
clock clk
reset rst

# Get design information to check general complexity
get_design_info

autoprove
