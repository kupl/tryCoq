import os
import argparse
import subprocess
import pandas as pd
import itertools

TOOLS = ['cclemma', 'thesy','dilemma']
BENCHMARKS = ['isaplanner', 'clam', 'optimization', 'dilemma']
TIMEOUT = 120

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
    
    parser.add_argument('--aggregate',
                        type = bool,
                        default = False,
                        help = 'Whether to aggregate results. Default is False.')

    parser.add_argument('--handshaking',
                        type = bool,
                        default = False,
                        help = 'Whether to use handshaking. Default is False.')
    return parser.parse_args()   

def run_dilemma(benchmark_name, handshaking):
    if benchmark_name == 'dilemma':
        benchmark_name = 'dilemma-bench'
    file_path = os.path.join('../dilemma-benchmark',benchmark_name,"dilemma")
    
    result_path = os.path.join('result', "dilemma", benchmark_name)
    os.makedirs(result_path, exist_ok=True)
    if not os.path.exists(file_path):
        print(f"Benchmark {benchmark_name} does not exist in the specified path: {file_path}")
        return    
    dir_list = os.listdir(file_path)

    if benchmark_name == 'dilemma-bench' and not handshaking:
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
                output_path_by_problem = os.path.join(output_dir, base + '.log')
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
                            f.write(f"Dilemma timed out for benchmark {benchmark_name} with problem {problem}.")
                            f.write(e.stderr.decode("utf-8"))
                except Exception as e:
                    with open(output_path_by_problem, "w") as f:
                        if e.stdout:
                                f.write(e.stdout.decode("utf-8"))
                        if e.stderr:                            
                            f.write(f"An error occurred while running Dilemma on benchmark {benchmark_name}: {e}")
                            f.write(e.stderr.decode("utf-8"))
    elif benchmark_name == 'dilemma-bench' and handshaking :
        for problem in dir_list:
            result_path = os.path.join('result','dilemma','dilemma-bench-handshaking')
            output_dir = os.path.join(result_path,problem)
            if not os.path.exists(output_dir):
                os.makedirs(output_dir, exist_ok=True)
            file_list = os.listdir(os.path.join(file_path, problem))
            input_file = os.path.join(file_path, problem, [i for i in file_list if i.endswith('input')][0])
            
            program_pairs = list(itertools.combinations([i for i in file_list if not i.endswith('input')], 2))
            for (program_a,program_b) in program_pairs:
                base_a, _ = os.path.splitext(program_a)
                base_b, _ = os.path.splitext(program_b)
                with open(input_file, 'r') as f:
                    lines = []
                    for line in f:
                        line = line.strip()
                        if line:
                            lines.append(line)
                    fname = lines[0]
                    types = lines[1:]
                    args = [f"inp{i}" for i in range(len(types))]
                    quantifiers = " ".join(f"({a} : {t})" for a,t in zip(args, types))
                    arglist = " ".join(args)
                    lhs = f"{fname}_{base_a} {arglist}".strip()
                    rhs = f"{fname}_{base_b} {arglist}".strip()
                    assertion = f"assert forall {quantifiers}, {lhs} = {rhs}"
                    print(assertion)
                output_path_by_problem = os.path.join(output_dir, base_a + '-' + base_b + '.log')
                program_a = os.path.join(file_path,problem,program_a)
                program_b = os.path.join(file_path, problem, program_b)
                input_text = '\n'.join([program_a, program_b, "2", assertion]) + '\n'
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
                            f.write(f"Dilemma timed out for benchmark {benchmark_name} with problem {problem}.")
                            f.write(e.stderr.decode("utf-8"))
                except Exception as e:
                    with open(output_path_by_problem, "w") as f:
                        if e.stdout:
                                f.write(e.stdout.decode("utf-8"))
                        if e.stderr:                            
                            f.write(f"An error occurred while running Dilemma on benchmark {benchmark_name}: {e}")
                            f.write(e.stderr.decode("utf-8"))
    elif benchmark_name == 'clam':
        definition_file = os.path.join(file_path, 'clam.ml')
        input_file = os.path.join(file_path, 'input')
        with open(input_file, 'r') as f:
            assertion = f.readlines()
        for i, problem in enumerate(assertion):
            problem = problem.strip()
            input_text = f"{definition_file}\n{definition_file}\n{2}\n{problem}\n"
            print(input_text)
            print(f"Problem {i+1}: {problem}")
            output_path_by_problem = os.path.join(result_path, "clam", f"problem{i+1}.log")
            try:
                result = subprocess.run(['opam', 'exec', '--', 'dune', 'exec', 'dilemma'], input=input_text, text=True, timeout=TIMEOUT, capture_output=True)
                with open(output_path_by_problem, "w") as f:
                    f.write(result.stdout)
                    f.write(result.stderr)
            except subprocess.TimeoutExpired as e:
                with open(output_path_by_problem, "w") as f:
                    if e.stdout:
                        f.write(e.stdout.decode("utf-8"))
                    if e.stderr:                            
                        f.write(f"Dilemma timed out for benchmark {benchmark_name} with problem {i+1}.")
                        f.write(e.stderr.decode("utf-8"))
            except Exception as e:
                with open(output_path_by_problem, "w") as f:
                    if e.stdout:
                        f.write(e.stdout.decode("utf-8"))
                    if e.stderr:                            
                        f.write(f"An error occurred while running Dilemma on benchmark {benchmark_name}: {e}")
                        f.write(e.stderr.decode("utf-8"))
    elif benchmark_name == 'optimization':
        for problem in dir_list:
            output_dir = os.path.join(result_path,problem)
            if not os.path.exists(output_dir):
                os.makedirs(output_dir, exist_ok=True)
            file_list = os.listdir(os.path.join(file_path, problem))
            input_file = os.path.join(file_path, problem, [i for i in file_list if i.endswith('input')][0])
            with open(input_file, 'r') as f:
                assertion = f.read()
            rest_programs = [i for i in file_list if  i.endswith('.ml')]
            for program in rest_programs:
                base, _ = os.path.splitext(program)
                output_path_by_problem = os.path.join(output_dir, base + '.log')
                program = os.path.join(file_path, problem, program)
                input_text = '\n'.join([program, program, assertion]) + '\n'
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
                            f.write(f"Dilemma timed out for benchmark {benchmark_name} with problem {problem}.")
                            f.write(e.stderr.decode("utf-8"))
                except Exception as e:
                    with open(output_path_by_problem, "w") as f:
                        if e.stdout:
                                f.write(e.stdout.decode("utf-8"))
                        if e.stderr:                            
                            f.write(f"An error occurred while running Dilemma on benchmark {benchmark_name}: {e}")
                            f.write(e.stderr.decode("utf-8"))
    else:
        print(f"Benchmark {benchmark_name} is not supported for Dilemma.")
        return


def get_proof_result(file_path):
    if not os.path.exists(file_path):
        return None
    with open(file_path, 'r') as f:
        content = f.read()
    if "Proof Success" in content:
        return "Proof Success"
    elif "Fatal error" in content:
        return 'error'
    else:
        return 'timeout'
    

def aggregate_results():
    benchmarks = os.listdir('./result/dilemma')
    for benchmark in benchmarks:
        output_path = os.path.join('./summary/summary_'+benchmark+'.md')
        with open(output_path, 'w') as md:
            benchmark_path = os.path.join('./result/dilemma', benchmark)
            files = os.listdir(benchmark_path)
            total_stats = {
                'success': 0,
                'error': 0,
                'timeout': 0,
                'total': 0
            }
            df_rows = []
            for file in files:
                file_path = os.path.join(benchmark_path, file)
                problems = os.listdir(file_path)
                success_count = 0
                error_count = 0
                timeout_count = 0
                for problem in problems:
                    problem_path = os.path.join(file_path, problem)
                    result = get_proof_result(problem_path)
                    if result == "Proof Success":
                        success_count += 1
                    elif result == "error":
                        error_count += 1
                    else:
                        timeout_count += 1
                df_rows.append({
                    "Problem": file,
                    "Success": success_count,
                    "Error": error_count,
                    "Timeout": timeout_count,
                    "Total": success_count + error_count + timeout_count
                })

                total_stats['success'] += success_count
                total_stats['error'] += error_count
                total_stats['timeout'] += timeout_count
                total_stats['total'] += success_count + error_count + timeout_count

            if df_rows:
                df = pd.DataFrame(df_rows).set_index("Problem")
                df.loc["Total"] = [
                    total_stats['success'],
                    total_stats['error'],
                    total_stats['timeout'],
                    total_stats['total']
                ]
                md.write(f"# Benchmark: {benchmark}\n\n")
                md.write(df.to_markdown() + '\n\n')
            else:
                md.write(f"# Benchmark: {benchmark}\n\n")
                md.write("No results found.\n\n")
            

                        
if __name__ == '__main__':
    args = parse_args()
    dataset_list = args.benchmarks
    tool_list = args.tools
    if args.aggregate:
        aggregate_results()
        exit(0)
    for tool in tool_list:    
        for dataset in dataset_list:
            if tool == 'dilemma':
                run_dilemma(dataset, args.handshaking)
            elif tool == 'cclemma':
                pass
            elif tool == 'thesy':
                pass
            else:
                print(f"Tool {tool} is not supported.")