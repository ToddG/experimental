#! /bin/bash

echo "----------------------------------------------------"
echo "Solution 1A"
echo "----------------------------------------------------"
tlc -dump dot solution1A.dot -config solution_1A.cfg logical_clock.tla && dot -Tpng solution1A.dot -o solution1A.png
echo "----------------------------------------------------"
echo "Solution 1B"
echo "----------------------------------------------------"
tlc -dump dot solution1B.dot -config solution_1B.cfg logical_clock.tla && dot -Tpng solution1B.dot -o solution1B.png
echo "----------------------------------------------------"
echo "Solution 2A"
echo "----------------------------------------------------"
tlc -dump dot solution2A.dot -config solution_2A.cfg logical_clock.tla && dot -Tpng solution2A.dot -o solution2A.png
echo "----------------------------------------------------"
echo "Solution 2B"
echo "----------------------------------------------------"
tlc -dump dot solution2B.dot -config solution_2B.cfg logical_clock.tla && dot -Tpng solution2B.dot -o solution2B.png
echo "----------------------------------------------------"
echo "Solution 3A"
echo "----------------------------------------------------"
tlc -dump dot solution3A.dot -config solution_3A.cfg logical_clock.tla && dot -Tpng solution3A.dot -o solution3A.png
echo "----------------------------------------------------"
echo "Solution 3B"
echo "----------------------------------------------------"
tlc -dump dot solution3B.dot -config solution_3B.cfg logical_clock.tla && dot -Tpng solution3B.dot -o solution3B.png
