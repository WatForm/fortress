import logging
import sys
import subprocess as sp

def print_usage(file = sys.stdout):
    text = f"""Checks if it is safe to merge a branch
        Usage: python3 {__file__} [args...] [branch-name]
        branch-name name of the branch to test. Uses current branch if omitted
        -h Show this message
        -v Show verbose logging
        --reset -r cleans the branch and master and resets to HEAD"""
    print(text, file=file)
    

args = sys.argv[1:]  # remove the file's name


if "-h" in args:
    print_usage()
    sys.exit(0)

verbose = "-v" in args

if verbose:
    args.remove("-v")
    logging.basicConfig(level=logging.DEBUG)
else:
    logging.basicConfig(level=logging.WARN)

if "--reset" in args:
    reset = True
    args.remove("--reset")
elif "-r" in args:
    reset = True
    args.remove("-r")
else:
    reset = False

if len(args) == 0:
    process = sp.run(["git", "branch", "--show-current"], capture_output=True)
    test_branch = str(process.stdout.strip().decode(encoding=sys.stdin.encoding))
elif len(args) == 1:
    test_branch = str(args[0])
if len(args) > 1:
    print("Got too many arguments!", file=sys.stderr)
    print_usage(file=sys.stderr)
    exit(1)

logging.info("Testing branch %s", test_branch)

if reset:
    print("I don't trust myself enough to script this.")
    print("Checkout whatever branch you want and run:")
    print("git reset --hard")
else:
    commands = [
        ['git', 'fetch'],
        ['git', 'checkout', test_branch],
        ['sbt', 'test'],
        ['git', 'pull'],
        ['git', 'checkout', 'master'],
        ['git', 'pull'],
        ['git', 'merge', test_branch],
        ['sbt', 'test'],
    ]

for command in commands:
    logging.info("Running command '%s'", ' '.join(command))
    testing = command[0] == 'sbt'
    capture = not testing and not verbose
    process = sp.run(command, capture_output=capture)
    if process.returncode != 0:
        print("\n\n\n")
        if not testing:
            logging.error("Got exit code %d from command %s", process.returncode, ' '.join(command))
            if capture:
                logging.error("STDOUT:\n%s\n\nSTDERR:\n%s", process.stdout, process.stderr)
        else:
            print("NOT READY, FIX TESTS", sys.stderr)
        sp.call(['git', 'status'])
        exit(1)

print("READY!")
exit(0)
