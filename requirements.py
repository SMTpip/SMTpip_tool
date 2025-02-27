import re


def parse_requirements(requirements_txt):
    """
    Parses the content of requirements.txt into a dictionary of packages and their version specifiers.
    Handles cases where version specifiers might include an "extra" part after a semicolon, and cases where there are no version specifiers.

    Parameters:
        requirements_txt (str): The content of the requirements.txt file as a single string.

    Returns:
        dict: A dictionary where keys are package names and values are lists of tuples representing version specifiers.
              If a package has no version specifiers, the value will be an empty list.
    """
    requirements = {}  # Initialize an empty dictionary to store package requirements
    lines = requirements_txt.strip().split("\n")  # Split the input string into lines
    for line in lines:  # Iterate through each line
        line = line.strip()  # Trim whitespace from the line
        if line:  # Check if the line is not empty
            # Split the line into parts based on version specifiers using a regular expression
            parts = re.split(r"([><!=]=?[\d.*]+(?:, )?)", line)
            # Extract the package name from the first part, handling extra parts after a semicolon
            package = parts[0].strip().split(";")[0].strip()
            version_specs = parts[
                1:
            ]  # Extract version specifiers from the remaining parts

            if not version_specs:  # If there are no version specifiers
                requirements[package] = (
                    []
                )  # Add the package with an empty list of specifiers
            else:
                for spec in version_specs:  # Iterate through each version specifier
                    if spec.strip():  # Trim whitespace from the specifier
                        # Match the specifier with a regular expression to extract the operator and version
                        match = re.match(r"([><!=]=?)([\d.*]+)", spec.strip())
                        if match:  # If the match is successful
                            operator, version = (
                                match.groups()
                            )  # Extract the operator and version
                            if (
                                package in requirements
                            ):  # If the package is already in the dictionary
                                requirements[package].append(
                                    (operator, version)
                                )  # Append the (operator, version) tuple to the list
                            else:
                                requirements[package] = [
                                    (operator, version)
                                ]  # Add the package with a new list containing the (operator, version) tuple
    return requirements  # Return the dictionary of requirements
