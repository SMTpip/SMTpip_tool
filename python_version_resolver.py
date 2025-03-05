import os
import requests
from packaging.specifiers import SpecifierSet  # To handle version constraints
from packaging.version import Version  # To sort and compare versions
import json

# Load your JSON file data into a Python dictionary
def load_python_versions_json(json_path):
    """
    Load the JSON file containing the Python versions.
    """
    with open(json_path, 'r') as f:
        return json.load(f)

def get_package_info(package_name, version):
    """
    Fetches package info from PyPI and returns the relevant fields.
    """
    url = f"https://pypi.org/pypi/{package_name}/{version}/json"
    response = requests.get(url)
    if response.status_code == 200:
        root = response.json()
        info = root['info']
        return {
            "package_name": info.get('name'),
            "version": info.get('version'),
            "python_version": info.get("requires_python")
        }
    else:
        return None

def merge_constraints(python_versions):
    """
    Merges Python version constraints from multiple packages.
    """
    combined_specifier = SpecifierSet()  # Empty SpecifierSet to merge constraints
    for version_info in python_versions:
        python_constraint = version_info.get("requires_python")
        if python_constraint:
            combined_specifier &= SpecifierSet(python_constraint)
    
    return combined_specifier

def filter_python_versions(constraints, python_versions_json):
    """
    Filters Python versions from JSON file based on the merged constraints.
    """
    available_versions = list(python_versions_json['projects']['python'].keys())
    
    # Filter based on the merged constraints
    valid_versions = [version for version in available_versions if version in constraints]
    
    return valid_versions

def get_latest_version(versions):
    """
    Sorts the list of versions and returns the latest version.
    """
    sorted_versions = sorted(versions, key=Version)
    return sorted_versions[-1]

def collect_python_versions(requirements):
    """
    Collects the Python version requirements for all packages in the requirements list.
    Each requirement should have a structure of (package_name, version).
    """
    python_versions = []
    for requirement in requirements:
        if len(requirement) == 2:  # Ensure there are exactly two items (package_name, version)
            package_name, version = requirement
            package_info = get_package_info(package_name, version)
            if package_info:
                python_versions.append({
                    "package_name": package_info["package_name"],
                    "version": package_info["version"],
                    "requires_python": package_info["python_version"]
                })
            else:
                python_versions.append({
                    "package_name": package_name,
                    "version": version,
                    "error": "Package information could not be fetched"
                })
        else:
            print(f"Invalid requirement format: {requirement}")

    return python_versions

def update_install_script(directory, latest_python_version):
    """
    Updates the installScript.txt file to include the latest Python version and preserve package list.
    """
    install_script_path = os.path.join(directory, "install_script.txt")
    
    # Read the current installScript.txt
    with open(install_script_path, 'r') as file:
        install_script_content = file.readlines()

    # Prepare the new contents with the python_version specified
    new_install_script = [f'# Specify Python version\n\npython_version=="{latest_python_version}"\n\n# List of package dependencies\n']
    new_install_script.extend(install_script_content)

    # Write back to the installScript.txt file
    with open(install_script_path, 'w') as file:
        file.writelines(new_install_script)
