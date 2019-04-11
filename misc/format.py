def initialType(s):
    if s in {"1", "2", "2ex", "3", "4", "5"}: return s
    else: return s[:-1]

def convertType(s):
    if s in {"1", "2", "2ex", "3", "4", "5"}: return s
    if s in {"2D", "2exD", "4D", "5D"}: return s[:-1] + "$^*$"
    if s in {"2P", "2exP", "4P", "5P"}: return s[:-1] + "$^P$"
    return "initialType::PROBLEM!"

def convertMapSymbol(s):
    s1 = s.strip().rstrip(">").lstrip("<").split("|")
    return "$\\langle {0}; {1}; {2}\\rangle$".format(*s1)

def newMapSymbol(v, f, p):
    vv = v.strip().rstrip("]").lstrip("[")
    ff = f.strip().rstrip("]").lstrip("[")
    pp = p.strip().rstrip("]").lstrip("[")
    return "$\\langle {0}; {1}; {2}\\rangle$".format(vv, ff, pp)

def fixType(s):
    if "_" in s:
        lst = s.strip().split("_")
        if len(lst) > 2:
            return "fixType::NAPAKA!"
        return "$" + lst[0] + "_{" + lst[1] + "}$"
    return s
def formatLine(fname, lineNo):
    with open(fname) as f:
        cnt = 0
        for line in f:
            cnt += 1;
            if cnt != lineNo:
                continue
            lst = line.strip().split(";")
            Id = lst[0]
            tran = lst[1]
            initGWType = initialType(lst[2])
            GWType = convertType(lst[2])
            mapSymInit = convertMapSymbol(lst[3])
            genus = lst[4]

            dmType = fixType(lst[7])
            v = lst[9]
            e = lst[12]
            f = lst[16]
            p = lst[19]
            nmapsym = newMapSymbol(lst[11], lst[18], lst[21])

            return "{0} & {1} & {2} & {3} & {4} & {5} & {6} & {7} & {8} & {9} & {10} & {11}\\\\\n\\hline\n".format(
                Id, tran, initGWType, GWType, genus, mapSymInit, dmType, v, e, f, p, nmapsym)

outfile = "izpis.txt"
with open(outfile, "wt") as f:
    f.write(formatLine("type1.csv", 29)) #ok
    
    f.write(formatLine("type2.csv", 20)) #ok
    f.write(formatLine("type2.csv", 742)) #ok
    f.write(formatLine("type2.csv", 63)) #ok

    f.write(formatLine("type3.csv", 73)) #ok

    f.write(formatLine("type2ex.csv", 146)) #ok
    f.write(formatLine("type2ex.csv", 12)) #ok
    f.write(formatLine("type2ex.csv", 4)) #ok
    
    f.write(formatLine("type5.csv", 2)) #ok
    f.write(formatLine("type5.csv", 27)) #ok
    f.write(formatLine("type5.csv", 26)) #ok

    f.write(formatLine("type4.csv", 86)) #ok
    f.write(formatLine("type4.csv", 1136)) #ok
    f.write(formatLine("type4.csv", 660)) #ok

            
