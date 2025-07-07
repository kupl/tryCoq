import os
import argparse
import subprocess

TOOLS = ['cclemma', 'thesy','dilemma']
BENCHMARKS = ['isaplanner', 'clam', 'optimization', 'dilemma']
TIMEOUT = 60

def parse_args():
    parser = argparse.ArgumentParser(description='Run benchmarks.')
    
    parser.add_argument('--tools',
                        type = str,
                        nargs = '+',
                        choices = TOOLS,
                        default = ['dilemma'],
                        help = 'List of tools to run. Default is all tools: ' + ', '.join(TOOLS))
    
    parser.add_argument('--benchmarks',
                        type = str,
                        nargs = '+',
                        choices = BENCHMARKS,
                        default = BENCHMARKS,
                        help = 'List of benchmarks to run. Default is all benchmarks: ' + ', '.join(BENCHMARKS))
    return parser.parse_args()   

def run_benchmark(benchmark_name, tool_name):
    if benchmark_name == 'dilemma':
        benchmark_name = 'dilemma-bench'
    file_path = os.path.join('../dilemma-benchmark',benchmark_name,tool_name)
    
    result_path = os.path.join('result', tool_name, benchmark_name)
    os.makedirs(result_path, exist_ok=True)
    if not os.path.exists(file_path):
        print(f"Benchmark {benchmark_name} does not exist in the specified path: {file_path}")
        return
    if tool_name == 'dilemma':        
        dir_list = os.listdir(file_path)
        if len(dir_list) < 2:
            print(f"Not enough files in {file_path} to run dilemma tool.")
            return
        for problem in dir_list:
            output_dir = os.path.join(result_path,problem)
            if not os.path.exists(output_dir):
                os.makedirs(output_dir, exist_ok=True)
            file_list = os.listdir(os.path.join(file_path, problem))
            input_file = os.path.join(file_path, problem, [i for i in file_list if i.endswith('input')][0])
            with open(input_file, 'r') as f:
                assertion = f.read()
            program_a = os.path.join(file_path, problem, [i for i in file_list if i.endswith('ta1.ml')][0])
            rest_programs = [i for i in file_list if (not i.endswith('ta1.ml')) and i.endswith('.ml')]
            for program_b in rest_programs:
                base, _ = os.path.splitext(program_b)
                output_path_by_problem = os.path.join(output_dir, base + '.out')
                program_b = os.path.join(file_path, problem, program_b)
                input_text = '\n'.join([program_a, program_b, assertion]) + '\n'
                print(f"Here is input text: {input_text}")
                try:
                    result = subprocess.run(['dune', 'exec', 'dilemma'],input=input_text,text=True,timeout=TIMEOUT,capture_output=True)
                    with open(output_path_by_problem,"w") as f:
                        f.write(result.stdout)
                        f.write(result.stderr)
                except subprocess.TimeoutExpired as e:
                    with open(output_path_by_problem, "w") as f:
                        if e.stdout:
                            f.write(e.stdout.decode("utf-8"))
                        if e.stderr:                            
                            f.write(f"Tool {tool_name} timed out for benchmark {benchmark_name} with problem {problem}.")
                            f.write(e.stderr.decode("utf-8"))
                except Exception as e:
                    with open(output_path_by_problem, "w") as f:
                        if e.stdout:
                                f.write(e.stdout.decode("utf-8"))
                        if e.stderr:                            
                            f.write(f"An error occurred while running tool {tool_name} on benchmark {benchmark_name}: {e}")
                            f.write(e.stderr.decode("utf-8"))
    if tool_name == 'cclemma':
        pass
    if tool_name == 'thesy':
        pass
                        
if __name__ == '__main__':
    args = parse_args()
    dataset_list = args.benchmarks
    tool_list = args.tools
    for tool in tool_list:    
        for dataset in dataset_list:
            run_benchmark(dataset, tool)