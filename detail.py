import os

path = "result/dilemma/clam/clam"


if os.path.exists(path):
    dir_list = os.listdir(path)
    result = {}
    for file in dir_list:
        if file.endswith(".log"):
            file_path = os.path.join(path, file)
            index = int(file.split("problem")[1].split(".")[0])
            with open(file_path, 'r') as f:
                content = f.read()
                if "Proof Success" in content:
                    result[index] = "Success"
                elif "timed out" in content:
                    result[index] = "Timed out"
                else:
                    result[index] = "Error"
    for key in sorted(result.keys()):
        print(f"Problem {key}: {result[key]}")