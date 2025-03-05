import os
import subprocess
import requests
from datetime import datetime
import time
from nbconvert import ScriptExporter
import argparse


def convert_ipynb_to_py(notebook_path):
    """
    Convert Jupyter notebook to Python script.
    """
    exporter = ScriptExporter()
    script, _ = exporter.from_filename(notebook_path)
    py_file_path = notebook_path.replace(".ipynb", ".py")
    with open(py_file_path, "w", encoding="utf-8") as py_file:
        py_file.write(script)
    print(f"Converted {notebook_path} to {py_file_path}")
    return py_file_path


def find_ipynb_files(project_path):
    """
    Find all Jupyter notebook (.ipynb) files in the project directory.
    """
    ipynb_files = []
    for root, dirs, files in os.walk(project_path):
        for file in files:
            if file.endswith(".ipynb"):
                ipynb_files.append(os.path.join(root, file))
    return ipynb_files


def generate_package_list(project_path):
    """
    Use pipreqs to get the list of required packages, including from converted ipynb files.
    """
    try:
        # Convert all .ipynb files to .py files
        ipynb_files = find_ipynb_files(project_path)
        converted_files = [convert_ipynb_to_py(nb) for nb in ipynb_files]

        # Get the output of pipreqs as a string
        result = subprocess.run(
            ["pipreqs", project_path, "--print"], capture_output=True, text=True, check=True
        )
        # Extract package names from the pipreqs output
        packages = [line.split("==")[0].strip() for line in result.stdout.splitlines()]
        print("Extracted Packages:")
        for package in packages:
            print(package)

        # Cleanup: Optionally delete the converted .py files
        for py_file in converted_files:
            if os.path.exists(py_file):
                os.remove(py_file)
                print(f"Deleted temporary file: {py_file}")

        return packages
    except subprocess.CalledProcessError as e:
        print(f"An error occurred while running pipreqs: {e}")
        return []


def get_pypi_versions(package_name, retries=3, delay=2):
    """
    Fetch all versions of a package from PyPI along with their release dates.
    """
    url = f"https://pypi.org/pypi/{package_name}/json"
    for attempt in range(retries):
        try:
            response = requests.get(url, timeout=10)
            if response.status_code == 200:
                data = response.json()
                versions = []
                for version, release_info in data["releases"].items():
                    if release_info:  # Check if release information is available
                        release_date = release_info[0]["upload_time"]
                        release_date = datetime.strptime(release_date, "%Y-%m-%dT%H:%M:%S")
                        versions.append((version, release_date))
                return versions
            else:
                print(f"Failed to fetch data for package: {package_name}")
        except requests.exceptions.RequestException as e:
            print(f"Error fetching data for {package_name}: {e}")
        time.sleep(delay)
    return []  # Return empty list if all retries fail


def get_closest_versions(package_name, repo_creation_date, last_update_date):
    """
    Get the closest versions of the package to the repository creation and last update dates.
    """
    versions = get_pypi_versions(package_name)
    if not versions:
        return None, None  # Handle packages with no version data

    closest_creation_version = None
    closest_update_version = None
    min_creation_diff = float("inf")
    min_update_diff = float("inf")

    for version, release_date in versions:
        creation_diff = abs((release_date - repo_creation_date).days)
        update_diff = abs((release_date - last_update_date).days)

        if creation_diff < min_creation_diff:
            min_creation_diff = creation_diff
            closest_creation_version = version

        if update_diff < min_update_diff:
            min_update_diff = update_diff
            closest_update_version = version

    return closest_creation_version, closest_update_version


def write_final_requirements(packages, repo_creation_date, last_update_date, output_path):
    """
    Write the new requirements.txt with version constraints based on the closest versions to the dates.
    """
    with open(output_path, "w") as file:
        for package in packages:
            creation_version, update_version = get_closest_versions(
                package, repo_creation_date, last_update_date
            )

            if creation_version and update_version:
                file.write(f"{package}>={creation_version},<={update_version}\n")
            else:
                # In case no versions were found, just write the package name without version constraints
                file.write(f"{package}\n")

        print(f"New requirements file created at {output_path}")


def read_dates_from_file(file_path):
    """
    Read repository creation and last update dates from a dates.txt file.
    """
    with open(file_path, "r") as file:
        lines = file.readlines()
        repo_creation_date = datetime.strptime(lines[0].strip(), "%Y-%m-%d")
        last_update_date = datetime.strptime(lines[1].strip(), "%Y-%m-%d")
    return repo_creation_date, last_update_date


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate requirements.txt with date-based version constraints.")
    parser.add_argument(
        "project_path", type=str, help="Path to the project directory containing .ipynb files and dates.txt"
    )
    args = parser.parse_args()

    project_path = args.project_path
    dates_file_path = os.path.join(project_path, "dates.txt")

    # Read the dates from the file
    repo_creation_date, last_update_date = read_dates_from_file(dates_file_path)

    # Confirm the dates have been read correctly
    print(f"Repository Creation Date: {repo_creation_date}")
    print(f"Last Update Date: {last_update_date}")

    # Continue with the rest of the process
    new_requirements_path = os.path.join(project_path, "requirements.txt")

    # Step 1: Generate the package list using pipreqs, including converted ipynb files
    packages = generate_package_list(project_path)

    # Step 2: Write the final new_requirements.txt with version constraints based on the closest versions to the key dates
    if packages:
        write_final_requirements(
            packages, repo_creation_date, last_update_date, new_requirements_path
        )
