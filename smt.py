import time
from z3 import Optimize, String, Or, Implies, And, set_param, Solver, unsat, sat, Sum, If, Bool, IntVal, AtMost

# Main
def generate_smt_expression(direct_dependencies, transitive_dependencies, ctx):
    """
    Generate an SMT (Satisfiability Modulo Theories) expression to handle package version constraints,
    including both direct and transitive dependencies, using an Optimize solver.

    Args:
    direct_dependencies (dict): A dictionary where keys are package names and values are lists of matching versions.
    transitive_dependencies (dict): A dictionary where keys are "package==version" and values are dictionaries of transitive dependencies.
    add_soft_clauses (bool): Flag to indicate whether to add soft clauses or not.

    Returns:
    tuple: An Optimize solver instance with the added constraints and the list of constraints.
    """
    # Initialize an Optimize solver to handle both hard and soft constraints
    solver = Optimize(ctx=ctx)
    constraints = []

    # Generate constraints for direct dependencies
    for package, versions in direct_dependencies.items():
        if isinstance(versions, list):
            # Create a constraint that the package version must be one of the specified versions
            # assert len(versions) > 0
            expressions = [String(package, ctx=ctx) == v for v in versions]
            if len(expressions) == 0:
                continue
            package_constraint = Or(expressions)
            constraints.append(package_constraint)
            # if add_soft_clauses:
            #     # Add soft constraints with weights for versions
            #     sorted_versions = sorted(
            #         versions, reverse=False
            #     )  # Sort versions to prioritize newer versions
            #     weight = 1
            #     for version in sorted_versions:
            #         # Add a soft constraint with increasing weight for newer versions
            #         solver.add_soft(String(package, ctx=ctx) == version, weight)
            #         weight += 1  # Increment the weight for the next version

    # # Generate constraints for transitive dependencies
    for package_version, dependencies in transitive_dependencies.items():
        if isinstance(dependencies, dict):
            # Split the package_version to get the package name and its version
            package, version = package_version.split("==")
            for dep_package, dep_versions in dependencies.items():
                # Create a constraint for each dependency that it must be one of the specified versions
                expressions = [
                    String(dep_package, ctx=ctx) == dep_version
                    for dep_version in dep_versions
                ]
                if len(expressions) == 0:
                    continue
                dependency_constraint = Or(expressions)
                constraints.append(
                    Implies(
                        String(package, ctx=ctx) == version,
                        dependency_constraint,
                        ctx=ctx,
                    )
                )
                # if add_soft_clauses:
                #     # Add soft constraints with weights for versions
                #     sorted_versions = sorted(
                #         dep_versions, reverse=False
                #     )  # Sort versions to prioritize newer versions
                #     weight = 1
                #     for dep_version in sorted_versions:
                #         # Add a soft constraint with increasing weight for newer versions
                #         solver.add_soft(
                #             String(dep_package, ctx=ctx) == dep_version, weight
                #         )
                #         weight += 1  # Increment the weight for the next version

    # Combine all constraints into a single final constraint
    assert len(constraints) > 0
    final_constraint = And(constraints)
    # final_constraint = simplify(And(constraints))
    solver.add(final_constraint)

    return solver


#  objective function without cardinality constraints
def generate_objective_smt_expression(direct_dependencies, transitive_dependencies, ctx, add_soft_clauses):
    """
    Generate an SMT expression with string variables, soft clauses for version preferences,
    and a soft clause to prefer not installing packages.

    Args:
        direct_dependencies (dict): Package names mapped to lists of matching versions.
        transitive_dependencies (dict): "package==version" keys mapped to dependency dicts.
        ctx: Z3 context.
        add_soft_clauses (bool): Flag to add soft clauses.

    Returns:
        Optimize: Solver instance with constraints and soft clauses.
    """
    solver = Optimize(ctx=ctx)
    constraints = []

    # Collect all packages and their versions
    all_packages = set(direct_dependencies.keys())
    transitive_versions = {}  # Store versions from transitive dependencies
    for pkg_ver, deps in transitive_dependencies.items():
        if isinstance(deps, dict):
            pkg = pkg_ver.split("==")[0]
            all_packages.add(pkg)
            if pkg not in transitive_versions:
                transitive_versions[pkg] = set()
            transitive_versions[pkg].add(pkg_ver.split("==")[1])
            for dep_pkg, dep_vers in deps.items():
                all_packages.add(dep_pkg)
                if dep_pkg not in transitive_versions:
                    transitive_versions[dep_pkg] = set()
                transitive_versions[dep_pkg].update(dep_vers)

    # Merge direct and transitive versions
    package_versions = {}
    for pkg in all_packages:
        versions = set(direct_dependencies.get(pkg, []))
        versions.update(transitive_versions.get(pkg, set()))
        package_versions[pkg] = sorted(versions) if versions else []

    # Declare string variables
    package_vars = {pkg: String(pkg, ctx=ctx) for pkg in all_packages}

    # Hard constraints for direct dependencies
    for package, versions in direct_dependencies.items():
        if versions:
            constraints.append(Or([package_vars[package] == v for v in versions]))

    # Hard constraints for transitive dependencies
    for package_version, dependencies in transitive_dependencies.items():
        if isinstance(dependencies, dict):
            package, version = package_version.split("==")
            for dep_package, dep_versions in dependencies.items():
                dep_constraint = Or([package_vars[dep_package] == v for v in dep_versions])
                constraints.append(Implies(package_vars[package] == version, dep_constraint))

    # Add all hard constraints
    if constraints:
        solver.add(And(constraints))

    # Add soft clauses
    if add_soft_clauses:
        for package, versions in package_versions.items():
            if versions:
                num_versions = len(versions)
                # Soft clause to prefer not installing the package
                not_installed = And([package_vars[package] != v for v in versions])
                solver.add_soft(not_installed, 1)
                # Soft clauses to prefer newer versions
                for i, version in enumerate(versions):
                    weight = i / num_versions  # rank(v_p) / |V(p)|
                    solver.add_soft(package_vars[package] == version, weight)

    return solver


#  objective function with cardinality constraints
# def generate_objective_smt_expression(direct_dependencies, transitive_dependencies, ctx, add_soft_clauses):
#     """
#     Generate an SMT expression with string variables, soft clauses for version preferences,
#     cardinality constraints, and a soft clause to prefer not installing packages.

#     Args:
#         direct_dependencies (dict): Package names mapped to lists of matching versions.
#         transitive_dependencies (dict): "package==version" keys mapped to dependency dicts.
#         ctx: Z3 context.
#         add_soft_clauses (bool): Flag to add soft clauses.

#     Returns:
#         Optimize: Solver instance with constraints and soft clauses.
#     """
#     solver = Optimize(ctx=ctx)
#     constraints = []

#     # Collect all packages and their versions
#     all_packages = set(direct_dependencies.keys())
#     transitive_versions = {}  # Store versions from transitive dependencies
#     for pkg_ver, deps in transitive_dependencies.items():
#         if isinstance(deps, dict):
#             pkg = pkg_ver.split("==")[0]
#             all_packages.add(pkg)
#             if pkg not in transitive_versions:
#                 transitive_versions[pkg] = set()
#             transitive_versions[pkg].add(pkg_ver.split("==")[1])
#             for dep_pkg, dep_vers in deps.items():
#                 all_packages.add(dep_pkg)
#                 if dep_pkg not in transitive_versions:
#                     transitive_versions[dep_pkg] = set()
#                 transitive_versions[dep_pkg].update(dep_vers)

#     # Merge direct and transitive versions
#     package_versions = {}
#     for pkg in all_packages:
#         versions = set(direct_dependencies.get(pkg, []))
#         versions.update(transitive_versions.get(pkg, set()))
#         package_versions[pkg] = sorted(versions) if versions else []

#     # Declare string variables and auxiliary Boolean variables for cardinality
#     package_vars = {pkg: String(pkg, ctx=ctx) for pkg in all_packages}
#     version_selected = {}  # Boolean variables for each package-version pair
#     for pkg in all_packages:
#         version_selected[pkg] = {v: Bool(f"{pkg}=={v}", ctx=ctx) for v in package_versions[pkg]}

#     # Link string variables to Boolean variables
#     for pkg in all_packages:
#         versions = package_versions[pkg]
#         if versions:
#             # Ensure string variable matches exactly one Boolean variable
#             constraints.append(Or([And(package_vars[pkg] == v, version_selected[pkg][v]) for v in versions]))
#             # Ensure Boolean variables are consistent with string variable
#             for v in versions:
#                 constraints.append(Implies(package_vars[pkg] == v, version_selected[pkg][v]))
#                 constraints.append(Implies(version_selected[pkg][v], package_vars[pkg] == v))

#     # Add cardinality constraints: at most one version per package
#     for pkg in all_packages:
#         versions = package_versions[pkg]
#         if versions:
#             solver.add(AtMost(*[version_selected[pkg][v] for v in versions], 1))

#     # Hard constraints for direct dependencies
#     for package, versions in direct_dependencies.items():
#         if versions:
#             constraints.append(Or([package_vars[package] == v for v in versions]))

#     # Hard constraints for transitive dependencies
#     for package_version, dependencies in transitive_dependencies.items():
#         if isinstance(dependencies, dict):
#             package, version = package_version.split("==")
#             for dep_package, dep_versions in dependencies.items():
#                 dep_constraint = Or([package_vars[dep_package] == v for v in dep_versions])
#                 constraints.append(Implies(package_vars[package] == version, dep_constraint))

#     # Add all hard constraints
#     if constraints:
#         solver.add(And(constraints))

#     # Add soft clauses
#     if add_soft_clauses:
#         for package, versions in package_versions.items():
#             if versions:
#                 num_versions = len(versions)
#                 # Soft clause to prefer not installing the package
#                 not_installed = And([package_vars[package] != v for v in versions])
#                 solver.add_soft(not_installed, 1)
#                 # Soft clauses to prefer newer versions
#                 for i, version in enumerate(versions):
#                     weight = i / num_versions  # rank(v_p) / |V(p)|
#                     solver.add_soft(package_vars[package] == version, weight)

#     return solver



# with minimization function

# def generate_smt_expression(
#     direct_dependencies, transitive_dependencies, ctx, add_soft_clauses, minimize_packages
# ):
#     """
#     Generate an SMT (Satisfiability Modulo Theories) expression to handle package version constraints,
#     including both direct and transitive dependencies, using an Optimize solver.

#     Args:
#     direct_dependencies (dict): A dictionary where keys are package names and values are lists of matching versions.
#     transitive_dependencies (dict): A dictionary where keys are "package==version" and values are dictionaries of transitive dependencies.
#     add_soft_clauses (bool): Flag to indicate whether to add soft clauses or not.
#     minimize_packages (bool): Flag to indicate whether to minimize the number of packages included in the solution.

#     Returns:
#     tuple: An Optimize solver instance with the added constraints and the list of constraints.
#     """
#     # Initialize an Optimize solver to handle both hard and soft constraints
#     solver = Optimize(ctx=ctx)
#     constraints = []
#     is_included_vars = {}  # Dictionary to store the binary inclusion variables

#     # Generate constraints for direct dependencies
#     for package, versions in direct_dependencies.items():
#         if isinstance(versions, list):
#             # Create a constraint that the package version must be one of the specified versions
#             expressions = [String(package, ctx=ctx) == v for v in versions]
#             if len(expressions) == 0:
#                 continue
#             package_constraint = Or(expressions)
#             constraints.append(package_constraint)
            
#             # Create and add binary inclusion variable with the same context
#             if minimize_packages:
#                 is_included_vars[package] = Bool(f'is_included_{package}', ctx=ctx)
#                 solver.add(Implies(is_included_vars[package], package_constraint))
#                 solver.add(Implies(package_constraint, is_included_vars[package]))

#             if add_soft_clauses:
#                 # Add soft constraints with weights for versions
#                 sorted_versions = sorted(
#                     versions, reverse=False
#                 )  # Sort versions to prioritize newer versions
#                 weight = 1
#                 for version in sorted_versions:
#                     # Add a soft constraint with increasing weight for newer versions
#                     solver.add_soft(String(package, ctx=ctx) == version, weight)
#                     weight += 1  # Increment the weight for the next version

#     # Generate constraints for transitive dependencies
#     for package_version, dependencies in transitive_dependencies.items():
#         if isinstance(dependencies, dict):
#             # Split the package_version to get the package name and its version
#             package, version = package_version.split("==")
#             for dep_package, dep_versions in dependencies.items():
#                 # Create a constraint for each dependency that it must be one of the specified versions
#                 expressions = [
#                     String(dep_package, ctx=ctx) == dep_version
#                     for dep_version in dep_versions
#                 ]
#                 if len(expressions) == 0:
#                     continue
#                 dependency_constraint = Or(expressions)
#                 constraints.append(
#                     Implies(
#                         String(package, ctx=ctx) == version,
#                         dependency_constraint,
#                     )
#                 )
                
#                 # Create and add binary inclusion variable for the dependent package with the same context
#                 if minimize_packages:
#                     if dep_package not in is_included_vars:
#                         is_included_vars[dep_package] = Bool(f'is_included_{dep_package}', ctx=ctx)
#                     solver.add(Implies(is_included_vars[dep_package], dependency_constraint))
#                     solver.add(Implies(dependency_constraint, is_included_vars[dep_package]))

#                 if add_soft_clauses:
#                     # Add soft constraints with weights for versions
#                     sorted_versions = sorted(
#                         dep_versions, reverse=False
#                     )  # Sort versions to prioritize newer versions
#                     weight = 1
#                     for dep_version in sorted_versions:
#                         # Add a soft constraint with increasing weight for newer versions
#                         solver.add_soft(
#                             String(dep_package, ctx=ctx) == dep_version, weight
#                         )
#                         weight += 1  # Increment the weight for the next version

#     # Combine all constraints into a single final constraint
#     assert len(constraints) > 0
#     final_constraint = And(constraints)
#     solver.add(final_constraint)

#     # Add the optimization objective to minimize the number of packages included, if the switch is enabled
#     if minimize_packages:
#         solver.minimize(Sum([If(is_included_vars[pkg], 1, 0) for pkg in is_included_vars]))

#     return solver




def verify_solution(solver, model):
    # Check if the solution satisfies all constraints
    for constraint in solver.assertions():
        satisfied = model.eval(constraint, model_completion=True)
        if not satisfied:
            return False
    return True


def smt_solver(solver, ctx):

    start_time = time.time()
    # set_param("smt.random_seed", 1)

    result = solver.check()

    if result == sat:
        model = solver.model()
        is_valid = verify_solution(solver, model)
        # print(model)
        print("Solution is valid:", is_valid)
        elapsed_time = time.time()
        return (
            {d.name(): model[d] for d in model.decls()},
            None,
            start_time,
            elapsed_time,
        )
    elif result == unsat:
        print("Not satisfiable.")

        set_param(proof=True)
        # ctx = Context()

        # Return the proof
        temp_solver = Solver(ctx=ctx)
        for clause in solver.assertions():
            temp_solver.add(clause)

        res = temp_solver.check()
        assert res == unsat
        proof = temp_solver.proof()

        return None, proof, None, None
    else:
        print("Solver result unknown.")
        return None, None, None, None
