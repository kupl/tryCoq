import csv
from pathlib import Path
from argparse import ArgumentParser
from collections import defaultdict

def main():
    parser = ArgumentParser()
    parser.add_argument("input_csv", type=Path, help="Path to the input CSV file")
    
    args = parser.parse_args()
    input_csv = args.input_csv
    
    ids = []
    results = defaultdict(dict)
    with input_csv.open() as f:
        reader = csv.reader(f)
        for _ , id_pair , result in reader:
            ida, idb = id_pair.split("-")
            ids.extend([ida, idb])
            results[ida][idb] = result
            results[idb][ida] = result
    ids = sorted(set(ids), key=lambda x:( int(x[2:]) - 10000) if x.startswith("ta") else int(x[3:]))
    for i, ida in enumerate(ids):
        for idb in ids[i+1:]:
            print(f"{ida}-{idb},{results[ida].get(idb, 'N/A')}")  
            
if __name__ == "__main__":
    main()