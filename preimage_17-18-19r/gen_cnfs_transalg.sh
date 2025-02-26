for f in ./*transalg*.alg
do
 echo "Processing $f"
 base_name=$(basename -- "$f" .alg)
 #echo $base_cnfname
 Transalg1.1.6 -i $f -o ${base_name}.cnf &
done
