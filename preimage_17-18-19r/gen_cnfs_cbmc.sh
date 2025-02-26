for f in ./*cbmc*.c
do
 echo "Processing $f"
 base_name=$(basename -- "$f" .c)
 #echo $base_cnfname
 cbmc $f --dimacs --outfile ${base_name}.cnf &> log_cbmc_${base_name} &
done
