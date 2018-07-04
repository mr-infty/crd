from sage.all import *
from LaTeXOutput import *
import sys

def main():
    if len(sys.argv) > 2:
        compute_cohomology_for_type(sys.argv[1], list(map(int, sys.argv[2:])))
    else:
        print "Usage: sage main.py <type> <list-of-ranks>\nFor example: sage main.py A 2 3 4\n"

if __name__ == '__main__':
    main()
