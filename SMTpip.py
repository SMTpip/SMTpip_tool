import os
import time
import logging
import argparse
from z3 import Context
from create_requirements import generate_requirements_txt, read_solution_file
from dependency import fetch_direct_dependencies, fetch_transitive_dependencies
from read import read_json_file, read_requirements
from requirements import parse_requirements
from smt import generate_smt_expression, smt_solver


# Import functionalities from python_version_resolver
from python_version_resolver import load_python_versions_json, collect_python_versions, merge_constraints, filter_python_versions, get_latest_version, update_install_script

def read_install_script(install_script_path):
    """
    Reads the generated installScript.txt file and parses package names and versions.
    Expects each line in installScript.txt to have the format 'package==version'.
    """
    with open(install_script_path, 'r') as file:
        lines = file.readlines()

    # Extract package name and version from each line and return as a list of tuples
    parsed_requirements = []
    for line in lines:
        if '==' in line:  # Check for 'package==version' format
            package, version = line.strip().split('==')
            parsed_requirements.append((package, version))
    
    return parsed_requirements


def setup_logging(directory, log_file):
    """
    Setup logging configuration.
    """
    os.makedirs(directory, exist_ok=True)
    logging.basicConfig(
        filename=os.path.join(directory, log_file),
        level=logging.INFO,
        format="%(asctime)s - %(levelname)s - %(message)s",
    )


def log_execution_time(action_name, start_time, end_time):
    """
    Log the execution time of a specific action.
    """
    logging.info(f"{action_name} execution time: {end_time - start_time:.2f} seconds")


def read_input_files(directory):
    """
    Read input files from the specified directory.
    """
    requirements_txt = read_requirements(directory)
    projects_data = read_json_file(os.getcwd())  # Use current working directory for projects_data
    logging.info("Input files successfully read.")
    return requirements_txt, projects_data


def main(directory):
    """
    Main function to execute the dependency resolution process.
    """
    log_file = "execution_log.txt"

    # Setup logging
    setup_logging(directory, log_file)
    print("Dependency resolution started. Check 'execution_log.txt' for detailed logs.")

    try:
        # Read files
        start_time = time.time()
        requirements_txt, projects_data = read_input_files(directory)
        end_time = time.time()
        log_execution_time("Reading files", start_time, end_time)

        # Parse requirements
        start_time = time.time()
        requirements = parse_requirements(requirements_txt)
        end_time = time.time()
        log_execution_time("Parsing requirements", start_time, end_time)

        # Fetch dependencies
        start_time = time.time()
        direct_dependencies = fetch_direct_dependencies(requirements, projects_data)
        transitive_dependencies = fetch_transitive_dependencies(direct_dependencies, projects_data)
        end_time = time.time()
        log_execution_time("Fetching dependencies", start_time, end_time)

        # Generate SMT expression
        ctx = Context()
        start_time = time.time()
        solver = generate_smt_expression(
            direct_dependencies, transitive_dependencies, ctx, add_soft_clauses=False, minimize_packages=False
        )
        end_time = time.time()
        log_execution_time("Generating SMT expression", start_time, end_time)

        # Save SMT expression
        smt_expression_file = os.path.join(directory, "SMT_expression.txt")
        with open(smt_expression_file, "w") as file:
            file.write(str(solver))
        logging.info(f"SMT expression saved to: {smt_expression_file}")

        # Solve SMT expression
        start_time = time.time()
        solution, proof, solve_start, solve_end = smt_solver(solver, ctx)
        end_time = time.time()
        log_execution_time("Solving SMT expression", solve_start, solve_end)

        if solution:
            # Save solution
            solution_file = os.path.join(directory, "string_solution.txt")
            with open(solution_file, "w") as file:
                file.write(str(solution))
            logging.info(f"Solution saved to: {solution_file}")

            # Generate install_script.txt
            start_time = time.time()
            solution_dict = read_solution_file(solution_file)
            generate_requirements_txt(solution_dict, directory, "install_script.txt")
            end_time = time.time()
            log_execution_time("Generating install_script.txt", start_time, end_time)
            logging.info(f"install_script.txt generated successfully.")
        else:
            proof_file = os.path.join(directory, "proof.txt")
            with open(proof_file, "w") as file:
                file.write(proof)
            logging.warning(f"No solution found. Proof saved to: {proof_file}")
            print("No solution found. Check proof file for details.")
        

        # Now read the installScript.txt to get the packages and versions
        install_script_path = os.path.join(directory, "install_script.txt")
        parsed_install_script = read_install_script(install_script_path)

        # Load Python versions from the same JSON file
        python_versions_data = projects_data  # Since it's the same file, just reuse `projects_data`

        # Collect Python versions based on package dependencies from the installScript.txt
        python_versions = collect_python_versions(parsed_install_script)

        # Merge the Python version constraints
        merged_constraints = merge_constraints(python_versions)

        # Filter compatible Python versions from JSON data
        valid_python_versions = filter_python_versions(merged_constraints, python_versions_data)

        # Get the latest Python version
        latest_python_version = get_latest_version(valid_python_versions)

        # Update the installScript.txt with the latest Python version
        update_install_script(directory, latest_python_version)


    except Exception as e:
        logging.error(f"An error occurred: {e}")
        print("An error occurred. Check 'execution_log.txt' for details.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Run dependency resolution script.")
    parser.add_argument(
        "-d",
        "--directory",
        type=str,
        required=True,
        help="Directory containing requirements.txt and other input files.",
    )
    args = parser.parse_args()

    main(args.directory)
