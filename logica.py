ET_CHAR = "∧"
OR_CHAR = "∨"
IF_CHAR = "→"
NOT_CHAR = "¬"


class FBF:
    # The Well Formulated Formula, eventually annotated with a sign
    def __str__(self):
        txt = self.sign if self.sign else ""
        if len(self.args) > 1:
            txt += "({} {} {})".format(str(self.args[0]),
                                       self.char,
                                       str(self.args[1]))
        else:
            txt += "({} {})".format(self.char,
                                    str(self.args[0]))
        return txt

    def __eq__(self, other):
        # Two formulas are equal only when variables and function are the same
        return self.args == other.args and self.char == other.char

    def closed(self, other):
        "Check if the formula is closed by the argument"
        T = {"T", "Tc"}
        F = {"F", "Fc"}
        return self == other and \
            ((self.sign in T and other.sign in F) or
             (self.sign in F and other.sign in T))

    def __hash__(self):
        return hash(str(self))


class Atom(FBF):
    def __init__(self, value):
        "The atomic element"
        self.args = value
        self.char = ""
        self.sign = ""

    def __str__(self):
        return self.sign + str(self.args)


class Et(FBF):
    def __init__(self, args, sign=None):
        "The logical et connector"
        self.char = ET_CHAR
        self.sign = sign
        self.args = list(map(lambda a: Atom(a) if isinstance(a, str) else a,
                             args))
        self.solver = "CL"
        if len(self.args) < 2:
            raise Exception("Object is not a valid formula")
        elif len(self.args) > 2:
            self = self.__init__([Et(args[0:2])] + args[2:])

    def solve(self):
        # just check a tableaux table
        fbf1, fbf2 = self.args
        fbf1.solver = self.solver
        fbf2.solver = self.solver
        if self.solver == "CL":
            if self.sign == "T":
                fbf1.sign = "T"
                fbf2.sign = "T"
                return [{fbf1, fbf2}]
            else:
                fbf1.sign = "F"
                fbf2.sign = "F"
                return [{fbf1}, {fbf2}]
        return self


class Or(FBF):
    def __init__(self, args, sign=None):
        "The logical Or connector"
        self.char = OR_CHAR
        self.sign = sign
        self.args = list(map(lambda a: Atom(a) if isinstance(a, str) else a,
                             args))
        self.solver = "CL"
        if len(self.args) < 2:
            raise Exception("Object is not a valid formula")
        elif len(self.args) > 2:
            self = self.__init__([Or(args[0:2])] + args[2:])

    def solve(self):
        fbf1, fbf2 = self.args
        fbf1.solver = self.solver
        fbf2.solver = self.solver
        if self.solver == "CL":
            if self.sign == "T":
                fbf1.sign = "T"
                fbf2.sign = "T"
                return [{fbf1}, {fbf2}]
            else:
                fbf1.sign = "F"
                fbf2.sign = "F"
                return [{fbf1, fbf2}]
        return self


class If(FBF):
    def __init__(self, args, sign=None):
        "The logical if connector"
        self.char = IF_CHAR
        self.sign = sign
        self.args = list(map(lambda a: Atom(a) if isinstance(a, str) else a,
                             args))
        self.solver = "CL"
        if len(self.args) < 2:
            raise Exception("Object is not a valid formula")
        elif len(self.args) > 2:
            self = self.__init__([If(args[0:2])] + args[2:])

    def solve(self):
        fbf1, fbf2 = self.args
        fbf1.solver = self.solver
        fbf2.solver = self.solver
        if self.solver == "CL":
            if self.sign == "T":
                fbf1.sign = "F"
                fbf2.sign = "T"
                return [{fbf1}, {fbf2}]
            else:
                fbf1.sign = "T"
                fbf2.sign = "F"
                return [{fbf1, fbf2}]
        return self


class Not(FBF):
    def __init__(self, args, sign=None):
        "The logical not operator"
        self.char = NOT_CHAR
        self.sign = sign
        self.args = list(map(lambda a: Atom(a) if isinstance(a, str) else a,
                             args))
        self.solver = "CL"
        if len(self.args) != 1:
            raise Exception("Object is not a valid formula")

    def solve(self):
        fbf = self.args[0]
        fbf.solver = self.solver
        if self.solver == "CL":
            fbf.sign = "F" if self.sign == "T" else "T"
            return [{fbf}]
        return self


class Tableaux:
    def __init__(self, S):
        if len(S) == 1:
            if not S[0].sign:
                S[0].sign = "F"
        self.S = set(S)

    def is_closed(self):
        for fbf in self.S:
            if any(map(lambda f: fbf.closed(f), self.S - {fbf})):
                return True
        return False


class TableauxCL(Tableaux):
    def __init__(self, S):
        super().__init__(S)
        self.solver = "CL"
        for s in self.S:
            s.solver = "CL"
        
    def apply_formula_to(self):
        # TODO: add an euristic
        not_atomic = set(filter(lambda f: not isinstance(f, Atom), self.S))
        if not not_atomic:
            return None
        s = not_atomic.pop()
        self.S -= {s}
        return s

    def solve(self, verbose=False):
        if verbose:
            print(", ".join([str(fbf) for fbf in self.S]))
        if self.is_closed():
            return True
        fbf = self.apply_formula_to()
        if not fbf:
            return False
        if verbose:
            print(" {}{} ".format(fbf.sign, fbf.char) + "-"*15)
        s = fbf.solve()
        if len(s) == 1:
            self.S |= s[0]
        else:
            return all([TableauxCL(list(self.S | t)).solve(verbose=verbose)
                        for t in s])
        return self.solve(verbose=verbose)


f = If(["A", "B", "A", "A", "B", "B"])
print(f, end=" :- ")
print(TableauxCL([f]).solve())

f = Or(["A", Not(["A"])])
print(f, end=" :- ")
print(TableauxCL([f]).solve())
