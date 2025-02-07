#!/bin/bash

# Define the values of N
values=(100 1000 5000 1000000)


# Iterate over the values of N
for N in "${values[@]}"; do
    # Create the input file
    input_file="input_${N}.txt"
    echo "1 ${N}" > "$input_file"
    
    # Call the command C and pipe the output to the output file
    output_file="output_${N}.txt"
    com = "cargo run --bin e2e --release -- --platform=sp1 --profiling=1 --structured-hints=${output_file} ceno_zkvm/examples/fibonacci.elf"
    $com > "$output_file"
done
