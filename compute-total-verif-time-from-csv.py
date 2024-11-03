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
    parser = argparse.ArgumentParser(description='Sum durations from the third column of a CSV file.')
    parser.add_argument('file_path', type=str, help='Path to the CSV file')
    args = parser.parse_args()

    total_duration = sum_durations(args.file_path)
    print(f"Total Duration: {total_duration}")

if __name__ == '__main__':
    main()
