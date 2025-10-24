import os


def print_graph(file_names):
    # create image from dot file and compine into a single image
    for file_name in file_names:
        print(f"Processing graph file: {file_name}")
        os.system(f"dot -Tpng {file_name} -o {file_name}.png")

def get_all_dot_files(directory):
    dot_files = []
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith('.dot'):
                dot_files.append(os.path.join(root, file))
    return dot_files
def main():
    directory = os.path.dirname(__file__)
    dot_files = get_all_dot_files(directory)
    if dot_files:
        print_graph(dot_files)
    else:
        print("No .dot files found in the directory.")
if __name__ == "__main__":
    main()