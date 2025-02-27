import time
from z3 import Optimize, String, Or, Implies, And, set_param, Solver, unsat, sat, Sum, If, Bool


# def generate_smt_expression(
#     direct_dependencies, transitive_dependencies, ctx, add_soft_clauses
# ):
#     """
#     Generate an SMT (Satisfiability Modulo Theories) expression to handle package version constraints,
#     including both direct and transitive dependencies, using an Optimize solver.

#     Args:
#     direct_dependencies (dict): A dictionary where keys are package names and values are lists of matching versions.
#     transitive_dependencies (dict): A dictionary where keys are "package==version" and values are dictionaries of transitive dependencies.
#     add_soft_clauses (bool): Flag to indicate whether to add soft clauses or not.

#     Returns:
#     tuple: An Optimize solver instance with the added constraints and the list of constraints.
#     """
#     # Initialize an Optimize solver to handle both hard and soft constraints
#     solver = Optimize(ctx=ctx)
#     constraints = []

#     # Generate constraints for direct dependencies
#     for package, versions in direct_dependencies.items():
#         if isinstance(versions, list):
#             # Create a constraint that the package version must be one of the specified versions
#             # assert len(versions) > 0
#             expressions = [String(package, ctx=ctx) == v for v in versions]
#             if len(expressions) == 0:
#                 continue
#             package_constraint = Or(expressions)
#             constraints.append(package_constraint)
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

#     # # Generate constraints for transitive dependencies
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
#                         ctx=ctx,
#                     )
#                 )
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
#     # final_constraint = simplify(And(constraints))
#     solver.add(final_constraint)

#     return solver



# with minimization function

def generate_smt_expression(
    direct_dependencies, transitive_dependencies, ctx, add_soft_clauses, minimize_packages
):
    """
    Generate an SMT (Satisfiability Modulo Theories) expression to handle package version constraints,
    including both direct and transitive dependencies, using an Optimize solver.

    Args:
    direct_dependencies (dict): A dictionary where keys are package names and values are lists of matching versions.
    transitive_dependencies (dict): A dictionary where keys are "package==version" and values are dictionaries of transitive dependencies.
    add_soft_clauses (bool): Flag to indicate whether to add soft clauses or not.
    minimize_packages (bool): Flag to indicate whether to minimize the number of packages included in the solution.

    Returns:
    tuple: An Optimize solver instance with the added constraints and the list of constraints.
    """
    # Initialize an Optimize solver to handle both hard and soft constraints
    solver = Optimize(ctx=ctx)
    constraints = []
    is_included_vars = {}  # Dictionary to store the binary inclusion variables

    # Generate constraints for direct dependencies
    for package, versions in direct_dependencies.items():
        if isinstance(versions, list):
            # Create a constraint that the package version must be one of the specified versions
            expressions = [String(package, ctx=ctx) == v for v in versions]
            if len(expressions) == 0:
                continue
            package_constraint = Or(expressions)
            constraints.append(package_constraint)
            
            # Create and add binary inclusion variable with the same context
            if minimize_packages:
                is_included_vars[package] = Bool(f'is_included_{package}', ctx=ctx)
                solver.add(Implies(is_included_vars[package], package_constraint))
                solver.add(Implies(package_constraint, is_included_vars[package]))

            if add_soft_clauses:
                # Add soft constraints with weights for versions
                sorted_versions = sorted(
                    versions, reverse=False
                )  # Sort versions to prioritize newer versions
                weight = 1
                for version in sorted_versions:
                    # Add a soft constraint with increasing weight for newer versions
                    solver.add_soft(String(package, ctx=ctx) == version, weight)
                    weight += 1  # Increment the weight for the next version

    # Generate constraints for transitive dependencies
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
                    )
                )
                
                # Create and add binary inclusion variable for the dependent package with the same context
                if minimize_packages:
                    if dep_package not in is_included_vars:
                        is_included_vars[dep_package] = Bool(f'is_included_{dep_package}', ctx=ctx)
                    solver.add(Implies(is_included_vars[dep_package], dependency_constraint))
                    solver.add(Implies(dependency_constraint, is_included_vars[dep_package]))

                if add_soft_clauses:
                    # Add soft constraints with weights for versions
                    sorted_versions = sorted(
                        dep_versions, reverse=False
                    )  # Sort versions to prioritize newer versions
                    weight = 1
                    for dep_version in sorted_versions:
                        # Add a soft constraint with increasing weight for newer versions
                        solver.add_soft(
                            String(dep_package, ctx=ctx) == dep_version, weight
                        )
                        weight += 1  # Increment the weight for the next version

    # Combine all constraints into a single final constraint
    assert len(constraints) > 0
    final_constraint = And(constraints)
    solver.add(final_constraint)

    # Add the optimization objective to minimize the number of packages included, if the switch is enabled
    if minimize_packages:
        solver.minimize(Sum([If(is_included_vars[pkg], 1, 0) for pkg in is_included_vars]))

    return solver




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
