#!/bin/bash

THEORIES_DIR="theories"
PROJECTS_DIR="projects"

mkdir -p "$PROJECTS_DIR"

# Function: find the actual file path for a theory name
find_theory_file() {
    local name="$1"
    for ext in ".theory" ".coh.theory" ".prop.theory" ".reg.theory" ".eq.theory" ".mereo.theory" ".fol.theory"; do
        if [ -f "$THEORIES_DIR/${name}${ext}" ]; then
            echo "$THEORIES_DIR/${name}${ext}"
            return 0
        fi
    done
    return 1
}

# Function: get direct dependencies of a theory file
get_direct_deps() {
    local file="$1"
    grep -oP '@\K[\w_]+' "$file" 2>/dev/null | sort -u
}

# Function: get transitive closure of dependencies (BFS)
get_all_deps_recursive() {
    local root_name="$1"
    local -A visited
    local queue=("$root_name")
    local deps=()
    
    while [ ${#queue[@]} -gt 0 ]; do
        local current="${queue[0]}"
        queue=("${queue[@]:1}")
        
        # Skip if already processed
        if [[ -n "${visited[$current]}" ]]; then
            continue
        fi
        visited["$current"]=1
        
        # Find the file for this dependency
        local current_file=$(find_theory_file "$current")
        if [ -z "$current_file" ]; then
            continue
        fi
        
        # Get direct dependencies of current theory
        local direct=$(get_direct_deps "$current_file")
        for dep in $direct; do
            if [[ -z "${visited[$dep]}" ]]; then
                queue+=("$dep")
                deps+=("$dep")
            fi
        done
    done
    
    # Return unique list
    printf '%s\n' "${deps[@]}" | sort -u
}

# Main loop over all theories
for theory_file in "$THEORIES_DIR"/*.theory; do
    # Extract base name (strip all extensions)
    theory_base=$(basename "$theory_file")
    theory_base="${theory_base%.theory}"
    theory_base="${theory_base%.coh}"
    theory_base="${theory_base%.prop}"
    theory_base="${theory_base%.reg}"
    theory_base="${theory_base%.eq}"
    theory_base="${theory_base%.mereo}"
    theory_base="${theory_base%.fol}"
    
    # Remove any trailing dots
    theory_base="${theory_base%.}"
    
    echo "========================================="
    echo "Project: $theory_base"
    
    # Create project folder
    project_dir="$PROJECTS_DIR/$theory_base"
    mkdir -p "$project_dir"
    
    # Copy main theory file
    cp "$theory_file" "$project_dir/"
    echo "  ✓ Copied main theory: $(basename "$theory_file")"
    
    # Get all recursive dependencies
    deps=$(get_all_deps_recursive "$theory_base")
    
    if [ -n "$deps" ]; then
        echo "  Dependencies:"
        for dep in $deps; do
            dep_file=$(find_theory_file "$dep")
            if [ -n "$dep_file" ]; then
                cp "$dep_file" "$project_dir/"
                echo "    ✓ Copied: $(basename "$dep_file")"
            else
                echo "    ✗ Warning: $dep not found" >&2
            fi
        done
    else
        echo "  No dependencies found."
    fi
    
    echo ""
done

echo "All projects created successfully!"
