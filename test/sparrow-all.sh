#!/bin/bash

# Get a list of subdirectories
subdirectories=$(find . -type d)

# Check if an argument was provided
if [ "$#" -eq 1 ]; then
    dir_array=($1)
    # Run the command only in the specified subdirectory
    for dir in "${dir_array[@]:0}"; do
        if [ -d "$dir" ]; then
            cd "$dir"
            sparrow -patron main.c > /dev/null 2>&1
            cd ..
        else
            echo "Subdirectory '$DIR' not found."
        fi
    done
else
    # Loop through each subdirectory
    for dir in $subdirectories; do
        # Check if 'main.c' file exists in the current subdirectory
        if [ -f "$dir/main.c" ]; then
            # Change to the subdirectory and run the 'sparrow -patron main.c' command
            cd "$dir"
            sparrow -patron main.c
            # Return to the original directory
            cd ..
        fi
    done
fi
