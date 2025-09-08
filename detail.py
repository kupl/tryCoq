import os

path = "result/dilemma/clam/clam"
path2 = "result/dilemma/dilemma-bench-handshaking"

benchmark = input("Which benchmark to check? (1: clam, 2: dilemma-bench-handshaking): ")
if benchmark == "1":
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
            
else:
    if os.path.exists(path2):
        dir_list = os.listdir(path2)
        result = {}
        for problem in dir_list:
            result[problem] = {}
            log_list = os.listdir(os.path.join(path2, problem))
            for file in log_list:
                if file.endswith(".log"):
                    file_path = os.path.join(path2, problem, file)
                    with open(file_path, 'r') as f:
                        content = f.read()
                        if "Proof Success" in content:
                            result[problem][file] = "Success"
                        elif "timed out" in content:
                            result[problem][file] = "Timed out"
                        else:
                            result[problem][file] = "Error"
        for key in sorted(result.keys()):
            for subkey in sorted(result[key].keys()):
                print(f"Problem {key}, Log {subkey}: {result[key][subkey]}")
