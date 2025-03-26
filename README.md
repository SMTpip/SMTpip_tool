# SMTpip: A Tool for Resolving Dependency Conflicts in Python Projects

## Overview

SMTpip is a powerful tool designed to assist developers in resolving dependency conflicts in Python projects. This guide provides a comprehensive walkthrough of using SMTpip, including installation instructions, usage scenarios, and practical examples.

## Getting Started

### Where to Find SMTpip

SMTpip is open-source and hosted on GitHub. You can access and download the tool from the following link:

https://github.com/SMTpip/SMTpip_tool.git

### System Requirements

Ensure the following requirements are met before using SMTpip:

- **Python**: Version 3.8 or later.


### Installation Instructions

Follow these steps to install SMTpip on your system:

```bash
# Clone the repository
git clone https://github.com/SMTpip/SMTpip_tool.git

# Install the required dependencies
pip install -r requirements.txt
```

Once installed, Extract the KGraph.json in the sane directory. SMTpip is ready to use.


## How to Use SMTpip

### Input Requirements

SMTpip accepts two types of input:

1. A directory containing the `requirements.txt` file of a Python project, such as the example folder in the repository.
2. A directory of the Python project itself, such as the `examplePythonProject` folder in the repository, if the `requirements.txt` file is missing.

### Command-Line Interface (CLI)

#### Using an Existing `requirements.txt` File

If the project already includes a `requirements.txt` file, use the following command:

```bash
python .\SMTpip.py -d .\example\
```

Here, the `-d` flag specifies the path to the `requirements.txt` file.

#### Generating `requirements.txt` When Missing

For projects without a `requirements.txt` file, generate one based on the project’s release and last update dates using:

```bash
python .\SMTpip_generate.py .\examplePythonProject\
```

Once the `requirements.txt` file is generated, you can resolve dependencies with:

```bash
python .\SMTpip.py -d .\examplePythonProject\
```

These commands allow users to handle projects with or without `requirements.txt` files, ensuring efficient dependency resolution.

## Usage Scenarios

### Resolving Conflicts Using an Existing `requirements.txt` File

When a project already has a `requirements.txt` file, SMTpip directly processes this file to identify and resolve any dependency conflicts.

- **Input**: Path to the `requirements.txt` file.
- **Processing**:
  - SMTpip analyzes the file and retrieves dependency metadata from the knowledge graph.
  - It formulates constraints into logical expressions and resolves them using an SMT solver.
- **Output**: An `install_scripts.txt` file containing all dependency packages with their compatible versions. This file ensures seamless installation of dependencies without conflicts.

*Refer to Figure (a) for a visual representation.*

### Handling Projects Without a `requirements.txt` File

For projects without a `requirements.txt` file, SMTpip provides an alternative workflow:

- **Input**: Project directory.
- **Processing**:
  1. Scans the project directory to identify third-party packages used in the code.
  2. Generates a `requirements.txt` file based on the project’s release and last update dates.
  3. Processes the generated `requirements.txt` file to resolve dependency conflicts.
- **Output**: A resolved `requirements.txt` file and an `install_scripts.txt` file containing compatible package versions.

*Refer to Figure (b) for a visual representation.*

Figure (a) and (b)
![Image](https://github.com/user-attachments/assets/b7acebf2-1175-41db-947a-f1582978e5a0)

## Figures

- **Figure (a)**: SMTpip processes an existing `requirements.txt` file to generate an `install_scripts.txt` file containing compatible dependency versions.
- **Figure (b)**: SMTpip handles projects without a `requirements.txt` file by extracting dependencies, generating the file, and resolving conflicts.

## Conclusion

SMTpip is a flexible and efficient tool for resolving dependency conflicts in Python projects. By supporting both structured and unstructured inputs, it ensures seamless integration into diverse workflows, empowering developers to maintain project stability with minimal effort.

