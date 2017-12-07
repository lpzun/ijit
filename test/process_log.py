import os

with open("./1.txt") as ins:
    seen = set()
    for line in ins:
        if "tau" not in line:
            continue;
        line_lower = line.lower()
        if line_lower in seen:
            print(line.strip())
        else:
            seen.add(line_lower)
    print "the already-seen elements\n"
    
    for line in seen:
        print line
        