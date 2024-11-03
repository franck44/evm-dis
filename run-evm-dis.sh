#!/bin/bash

# Check if no arguments are provided
if [ $# -eq 0 ]; then
    java -jar build/libs/Driver-java/evmdis.jar --help
    exit 0
fi

# Get all arguments except the last one
args=("${@:1:$#-1}")

# Get the last argument
last_arg="${!#}"

# Check if the last argument is a file and exists
if [ ! -f "$last_arg" ]; then
    if [ "$last_arg" != "--help" ]; then
        echo "Error: The last argument must be a file that exists or --help."
        exit 1
    else
        java -jar build/libs/Driver-java/evmdis.jar --help
        exit 0
    fi
fi
# last argument is a file and exists 

# Process the last argument to replace its extension
shortname=$(basename -- "$last_arg")
extension="${last_arg##*.}"
filename="${last_arg%.*}"

# Print the processing information
echo "Processing file: $last_arg"
echo "Shortname: $shortname"

# Read the contents of the last argument (file) into a variable
file_contents=$(cat "$last_arg")

# Execute the command with modified last argument that contains the string in the file
java -jar build/libs/Driver-java/evmdis.jar  "${args[@]}" "$file_contents"

