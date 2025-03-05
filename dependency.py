import re


def version_satisfies(version, spec):

    operator, spec_version = spec
    if operator == "==":
        return re.match(spec_version.replace("*", ".*"), version) is not None
    elif operator == "!=":
        return re.match(spec_version.replace("*", ".*"), version) is None
    elif operator == ">":
        return version > spec_version
    elif operator == ">=":
        return version >= spec_version
    elif operator == "<":
        return version < spec_version
    elif operator == "<=":
        return version <= spec_version
    return False


def find_matching_versions(package, specs, projects_data):

    if package not in projects_data:
        return []

    versions = projects_data[package].keys()  # Get all versions of the package
    matching_versions = []
    for version in versions:
        if all(version_satisfies(version, spec) for spec in specs):
            matching_versions.append(version)  # Add version if it satisfies all specs
    return matching_versions


def fetch_direct_dependencies(requirements, projects_data):

    direct_dependencies = {}

    for package, specs in requirements.items():
        matching_versions = find_matching_versions(
            package, specs, projects_data["projects"]
        )
        direct_dependencies[package] = (
            matching_versions  # Store matching versions for the package
        )

    return direct_dependencies


def parse_dependency(dependency):
    """
    Parse a dependency string into a package and a list of version specifiers.

    Parameters:
        dependency (str): A string representing a package and its version specifiers.

    Returns:
        tuple: A tuple where the first element is the package name and the second element is a list of tuples representing version specifiers.
    """
    # Split the dependency string into parts based on version specifiers using a regular expression
    parts = re.split(r"([><!=]=?[\d.*]+(?:, )?)", dependency)
    # Extract the package name from the first part, handling extra parts after a semicolon
    package = parts[0].strip().split(";")[0].strip()
    version_specs = []  # Initialize an empty list to store version specifiers

    # Iterate through the remaining parts
    for spec in parts[1:]:
        if spec.strip():  # Trim whitespace from the specifier
            # Match the specifier with a regular expression to extract the operator and version
            match = re.match(r"([><!=]=?)([\d.*]+)", spec.strip())
            if match:  # If the match is successful
                operator, version = match.groups()  # Extract the operator and version
                version_specs.append(
                    (operator, version)
                )  # Append the (operator, version) tuple to version_specs

    return package, version_specs  # Return the package and version_specs

#original
def fetch_transitive_dependencies(direct_dependencies, projects_data):
    """
    Recursively fetch transitive dependencies for each version of the packages in direct dependencies.

    Parameters:
        direct_dependencies (dict): A dictionary of direct dependencies where keys are package names and values are lists of versions.
        projects_data (dict): A dictionary containing project data, including available versions and their dependencies.

    Returns:
        dict: A dictionary where keys are package versions and values are dictionaries of transitive dependencies.
    """
    transitive_dependencies = (
        {}
    )  # Initialize an empty dictionary to store transitive dependencies

    def _fetch(package, version):
        key = f"{package}=={version}"  # Create a key as "package==version"
        if (
            key in transitive_dependencies
        ):  # If the key is already in transitive_dependencies, return the stored value
            return transitive_dependencies[key]

        # Handle case sensitivity for package lookup
        version_data = projects_data["projects"].get(package, {}).get(version, {})
        if (
            not version_data
        ):  # If version_data is empty, try lowercase version of the package name
            version_data = (
                projects_data["projects"].get(package.lower(), {}).get(version, {})
            )

        dependencies = {}  # Initialize an empty dictionary to store dependencies
        if version_data.get(
            "dependency_packages"
        ):  # If version_data contains dependency_packages
            for dep in version_data["dependency_packages"]:
                dep_package, dep_specs = parse_dependency(
                    dep
                )  # Parse dep to get dep_package and dep_specs

                # Handle case sensitivity for dependency package lookup
                matching_versions = []
                if (
                    not dep_specs
                ):  # If no version specifiers are provided, fetch all versions of the dependency package
                    matching_versions = list(
                        projects_data["projects"].get(dep_package, {}).keys()
                    )
                    if (
                        not matching_versions
                    ):  # Try lowercase version of the dependency package name if no versions found
                        matching_versions = list(
                            projects_data["projects"]
                            .get(dep_package.lower(), {})
                            .keys()
                        )
                else:  # If there are version specifiers, fetch matching versions of the dependency package
                    matching_versions = find_matching_versions(
                        dep_package, dep_specs, projects_data["projects"]
                    )

                if (
                    matching_versions
                ):  # Only include dependencies that have matching versions
                    dependencies[dep_package] = (
                        matching_versions  # Add dep_package with matching versions to dependencies
                    )
                    for (
                        dep_version
                    ) in (
                        matching_versions
                    ):  # Recursively fetch dependencies for each matching version
                        _fetch(dep_package, dep_version)

        # Only assign non-empty dependencies to transitive_dependencies
        if dependencies:
            transitive_dependencies[key] = dependencies

        return dependencies  # Return the dependencies for this package and version

    for (
        package,
        versions,
    ) in direct_dependencies.items():  # Iterate through direct dependencies
        for version in versions:  # Iterate through each version of the package
            _fetch(
                package, version
            )  # Fetch transitive dependencies for the package and version

    return transitive_dependencies  # Return the transitive dependencies dictionary


#with counting the depth
def fetch_transitive_dependencies_with_depth(direct_dependencies, projects_data):
    """
    Recursively fetch transitive dependencies for each version of the packages in direct dependencies.
    Tracks the depth of the recursion and counts the unique number of packages and versions encountered.

    Parameters:
        direct_dependencies (dict): A dictionary of direct dependencies where keys are package names and values are lists of versions.
        projects_data (dict): A dictionary containing project data, including available versions and their dependencies.

    Returns:
        dict: A dictionary where keys are package versions and values are dictionaries of transitive dependencies.
        int: The maximum depth of dependencies encountered.
        int: The total number of unique packages involved.
        int: The total number of unique versions involved.
    """
    transitive_dependencies = {}
    max_depth = 0
    visited_versions = set()  # Set to track unique (package, version) pairs

    def _fetch(package, version, depth):
        nonlocal max_depth
        key = f"{package}=={version}"
        
        # Update maximum depth
        max_depth = max(max_depth, depth)

        # If the package-version combo is already processed, return the cached value
        if key in transitive_dependencies:
            return transitive_dependencies[key]
        
        # Add to visited versions
        visited_versions.add((package, version))

        # Fetch version data, handling case sensitivity
        version_data = projects_data["projects"].get(package, {}).get(version, {})
        if not version_data:
            version_data = projects_data["projects"].get(package.lower(), {}).get(version, {})

        # Initialize dependencies for this package version
        dependencies = {}

        if version_data.get("dependency_packages"):
            for dep in version_data["dependency_packages"]:
                dep_package, dep_specs = parse_dependency(dep)

                # Fetch matching versions for the dependency
                matching_versions = []
                if not dep_specs:
                    matching_versions = list(projects_data["projects"].get(dep_package, {}).keys())
                    if not matching_versions:
                        matching_versions = list(projects_data["projects"].get(dep_package.lower(), {}).keys())
                else:
                    matching_versions = find_matching_versions(dep_package, dep_specs, projects_data["projects"])

                if matching_versions:
                    dependencies[dep_package] = matching_versions

                    # Recursively fetch dependencies for each matching version and increase the depth
                    for dep_version in matching_versions:
                        _fetch(dep_package, dep_version, depth + 1)

        # Store in transitive_dependencies even if there are no further dependencies
        transitive_dependencies[key] = dependencies

        return dependencies

    # Iterate through direct dependencies and process each version
    for package, versions in direct_dependencies.items():
        for version in versions:
            _fetch(package, version, 1)

    # Calculate the total number of unique packages and versions
    total_unique_packages = len({pkg for pkg, _ in visited_versions})
    total_unique_versions = len(visited_versions)

    return transitive_dependencies, max_depth, total_unique_packages, total_unique_versions
