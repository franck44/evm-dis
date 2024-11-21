import csv
import argparse
from datetime import timedelta


def parse_duration(duration_str):
    # Parse the duration string into a timedelta object
    h, m, s = map(float, duration_str.split(':'))
    return timedelta(hours=h, minutes=m, seconds=s)

def sum_durations(file_path):
    total_duration = timedelta()
    
    with open(file_path, mode='r') as file:
        reader = csv.reader(file)
        next(reader)  # Skip the header row
        
        for row in reader:
            duration_str = row[2]
            total_duration += parse_duration(duration_str)
    
    return total_duration

def main():
    parser = argparse.ArgumentParser(description='Sum durations from the third column of CSV files listed in an input file.')
    parser.add_argument('input_file', type=str, help='Path to the input file containing CSV filenames')
    parser.add_argument('output_file', type=str, help='Path to the output file to save the results')
    args = parser.parse_args()

    results = []

    with open(args.input_file, mode='r') as file:
        for line in file:
            file_path = line.strip()
            # if file_path.endswith('.csv'):
            # csv_file = replace_extension(file_path, "csv")
            input_file = f"build/proofs/etherscan/{file_path}/{file_path}-cfg-verification-stats.csv"
            total_duration = sum_durations(input_file)
            # total_duration = 0
            print(f"file {file_path} {total_duration}")
            results.append((file_path, total_duration))

    with open(args.output_file, mode='w') as file:
        writer = csv.writer(file)
        writer.writerow(['File', 'Total Duration'])
        for file_path, total_duration in results:
            writer.writerow([file_path, total_duration])

    print(f"Results saved to {args.output_file}")

if __name__ == '__main__':
    main()
    