import ast
import os


def read_solution_file(file_path):
    """
    Read the content of the solution file and parse it into a dictionary.

    Args:
        file_path (str): The path to the solution file.

    Returns:
        dict: A dictionary where keys are package names and values are version strings.
    """
    with open(file_path, "r") as file:
        content = file.read()
        solution_dict = ast.literal_eval(
            content
        )  # Safely evaluate the string to a dictionary
    return solution_dict


def generate_requirements_txt(solution, directory, filename="requirements.txt"):
    """
    Generate a requirements.txt file from the solution dictionary.

    Args:
        solution (dict): A dictionary where keys are package names and values are version strings.
        filename (str): The name of the requirements file to generate.
    """

    with open(os.path.join(directory, filename), "w") as file:
        for package, version in solution.items():
            if version:  # Only include packages with versions
                file.write(f"{package}=={version}\n")
