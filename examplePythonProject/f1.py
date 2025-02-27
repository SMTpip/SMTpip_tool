import time
import torch as pt
from z3 import Int, Solver

def fetch_data(url):
    try:
        response = requests.get(url)
        response.raise_for_status()  # Raise exception for HTTP errors
        print(f"Data fetched from {url}: {response.text[:100]}...")
    except requests.exceptions.RequestException as e:
        print(f"Error fetching data: {e}")

def tensor_operations():
    print("\nPerforming tensor operations with PyTorch:")
    # Create two tensors
    tensor_a = pt.tensor([1.0, 2.0, 3.0])
    tensor_b = pt.tensor([4.0, 5.0, 6.0])

    # Perform addition
    tensor_sum = tensor_a + tensor_b
    print(f"Tensor A: {tensor_a}")
    print(f"Tensor B: {tensor_b}")
    print(f"Sum: {tensor_sum}")

def z3_solver_example():
    print("\nSolving a constraint problem with Z3:")
    x = Int('x')
    y = Int('y')

    # Create a solver
    solver = Solver()

    # Add constraints
    solver.add(x + y == 10, x - y == 2)

    # Check if the constraints are satisfiable
    if solver.check() == 'sat':
        print(f"Solution found: {solver.model()}")
    else:
        print("No solution found.")

def main():
    start_time = time.time()

    # 1. Fetch data using requests
    url = "https://jsonplaceholder.typicode.com/posts/1"
    fetch_data(url)

    # 2. Perform PyTorch tensor operations
    tensor_operations()

    # 3. Solve a small problem using Z3 solver
    z3_solver_example()

    end_time = time.time()
    print(f"\nProcessing completed in {end_time - start_time:.2f} seconds.")

if __name__ == "__main__":
    main()

