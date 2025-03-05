import json
import os

def read_requirements(directory):
    """
    Reads the content of the `requirements.txt` file from a specified directory.

    Parameters:
        directory (str): The path to the directory containing the `requirements.txt` file.

    Returns:
        str: The content of the `requirements.txt` file as a single string.
    """
    with open(os.path.join(directory, "requirements.txt"), "r") as file:
        return file.read()
    

def read_test_requirements(directory):
    """
    Reads the content of either the `requirements.txt` or `date_based_requirements.txt` file 
    from a specified directory, based on user input.

    Parameters:
        directory (str): The path to the directory containing the requirements files.

    Returns:
        str: The content of the selected requirements file as a single string.
    """
    # Ask user which file to read
    choice = input("Which type of file would you like to read? Enter '1' for requirements.txt or '2' for date_based_requirements.txt: ")
    
    # Determine the file based on the user's choice
    if choice == '1':
        file_name = "requirements.txt"
    elif choice == '2':
        file_name = "date_based_requirements.txt"
    else:
        print("Invalid choice. Defaulting to requirements.txt.")
        file_name = "requirements.txt"
    
    # Read and return the content of the selected file
    file_path = os.path.join(directory, file_name)
    
    try:
        with open(file_path, "r") as file:
            return file.read()
    except FileNotFoundError:
        return f"Error: {file_name} not found in the directory."



# Function to read the JSON file from a directory
def read_json_file(directory, filename="KGraph.json"):
    """
    Reads the content of a JSON file from a specified directory.

    Parameters:
        directory (str): The path to the directory containing the JSON file.
        filename (str): The name of the JSON file to read. Default is 'updated_formated_8k.json'.

    Returns:
        dict: The content of the JSON file as a dictionary.
    """
    with open(os.path.join(directory, filename), "r") as file:
        return json.load(file)
