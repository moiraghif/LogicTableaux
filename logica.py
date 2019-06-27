ET_CHAR = "∧"
OR_CHAR = "∨"
IF_CHAR = "→"
NOT_CHAR = "¬"


class FBF:
    # The Well Formulated Formula, eventually annotated with a sign
    def __str__(self):
        txt = self.sign if self.sign else ""
        if len(self.args) > 1 and self.char:
            fbf1 = "({})".format(str(self.args[0])) if self.args[0].char \
                else str(self.args[0])
            fbf2 = "({})".format(str(self.args[1])) if self.args[1].char \
                else str(self.args[1])
            txt += "{} {} {}".format(fbf1, self.char, fbf2)
        elif self.char:
            fbf = "({})".format(str(self.args[0])) if self.args[0].char \
                else str(self.args[0])
            txt += "{}{}".format(self.char, fbf)
        else:
            txt += str(self.args)
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
        fbf1, fbf2 = self.args.copy()
        fbf1.solver = self.solver
        fbf2.solver = self.solver
        if self.solver == "CL":
            if self.sign == "T":
                fbf1.sign = "T"
                fbf2.sign = "T"
                return [{fbf1, fbf2}]
            elif self.sign == "F":
                fbf1.sign = "F"
                fbf2.sign = "F"
                return [{fbf1}, {fbf2}]
        elif self.solver == "INT":
            if self.sign == "T":
                fbf1.sign = "T"
                fbf2.sign = "T"
                return [{fbf1, fbf2}], [False]
            elif self.sign == "F":
                fbf1.sign = "F"
                fbf2.sign = "F"
                return [{fbf1}, {fbf2}], [False, False]
            elif self.sign == "Fc":
                fbf1.sign = "Fc"
                fbf2.sign = "Fc"
                return [{fbf1}, {fbf2}], [False, False]
            else:
                return [{self}], False
        return [{self}]


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
        fbf1, fbf2 = self.args.copy()
        fbf1.solver = self.solver
        fbf2.solver = self.solver
        if self.solver == "CL":
            if self.sign == "T":
                fbf1.sign = "T"
                fbf2.sign = "T"
                return [{fbf1}, {fbf2}]
            elif self.sign == "F":
                fbf1.sign = "F"
                fbf2.sign = "F"
                return [{fbf1, fbf2}]
        elif self.solver == "INT":
            if self.sign == "T":
                fbf1.sign = "T"
                fbf2.sign = "T"
                return [{fbf1}, {fbf2}], [False, False]
            elif self.sign == "F":
                fbf1.sign = "F"
                fbf2.sign = "F"
                return [{fbf1, fbf2}], [False]
            elif self.sign == "Fc":
                fbf1.sign = "Fc"
                fbf2.sign = "Fc"
                return [{fbf1, fbf2}], [False]
            else:
                return [{self}], False
        return [{self}]


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
        fbf1, fbf2 = self.args.copy()
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
        if self.solver == "INT":
            if self.sign == "T":
                if not fbf1.char:
                    fbf1.sign = "F"
                    fbf2.sign = "T"
                    return [{fbf1}, {fbf2}], [False, False]
                elif fbf1.char == ET_CHAR:
                    fbf = If([fbf1.args[0],
                              If([fbf1.args[1], fbf2])],
                             sign="T")
                    return [{fbf}], [False]
                elif fbf1.char == OR_CHAR:
                    fbf1_new = If([fbf1.args[0], fbf2], sign="T")
                    fbf2_new = If([fbf1.args[1], fbf2], sign="T")
                    return [{fbf1_new, fbf2_new}], [False]
                elif fbf1.char == IF_CHAR:
                    fbf1.sign = "T"
                    fbf_new = If([fbf1.args[1], fbf2], sign="F")
                    fbf2.sign = "T"
                    return [{fbf1, fbf_new}, {fbf2}], [False, False]
                else:
                    fbf1.sign = "F"
                    fbf2.sign = "T"
                    return [{self, fbf1}, {fbf2}], [False, False]
            elif self.sign == "F":
                fbf1.sign = "T"
                fbf2.sign = "F"
                return [{fbf1, fbf2}], [True]
            elif self.sign == "Fc":
                fbf1.sign = "T"
                fbf2.sign = "Fc"
                return [{fbf1, fbf2}], [True]
            else:
                return [{self}], [False]
        return [{self}]


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
        fbf = self.args.copy()[0]
        fbf.solver = self.solver
        if self.solver == "CL":
            fbf.sign = "F" if self.sign == "T" else "T"
            return [{fbf}]
        elif self.solver == "INT":
            if self.sign == "T":
                fbf.sign = "Fc"
                return [{fbf}], [False]
            elif self.sign == "F" or self.sign == "Fc":
                fbf.sign = "T"
                return [{fbf}], [True]
            else:
                return [{self}], [False]
        return [{self}]


class Tableaux:
    def __init__(self, S, solver):
        self.solver = solver
        if len(S) == 1 and not S[0].sign:
            S[0].sign = "F"
        self.S = set(S)
        for s in self.S:
            s.solver = self.solver

    def is_closed(self):
        for fbf in self.S:
            if any(map(lambda f: fbf.closed(f), self.S - {fbf})):
                return True
        return False


class TableauxCL(Tableaux):
    def __init__(self, S):
        super().__init__(S, "CL")

    def apply_formula_to(self):
        # TODO: add an euristic
        splits = {"T" + OR_CHAR,
                  "T" + IF_CHAR,
                  "F" + ET_CHAR}
        not_atomic = set(filter(lambda f: f.char, self.S))
        if not not_atomic:
            return None
        not_split_rules = set(filter(lambda f: f.sign + f.char not in splits,
                                     not_atomic))
        s = not_split_rules.pop() if not_split_rules else not_atomic.pop()
        self.S -= {s}
        return s

    def solve(self, verbose=False):
        if verbose:
            print(", ".join([str(fbf) for fbf in self.S]))
        if self.is_closed():
            if verbose:
                print(" closed " + "-"*11)
            return True
        fbf = self.apply_formula_to()
        if not fbf:
            if verbose:
                print(" not closed " + "-"*7)
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


class TableauxINT(Tableaux):
    def __init__(self, S, certain=False, old_S=set()):
        self.certain_sign = {"T", "Fc"}
        super().__init__(S, "INT")
        if certain:
            self.S = set(filter(lambda f: f.sign in self.certain_sign,
                                self.S))
        self.old_S = old_S

    def all_atomic(self):
        return all(map(lambda x: not x.char, self.S))

    def solve(self, verbose=False):
        # TODO: implementare questa cazzo di funzione
        if self.is_closed():
            if verbose:
                print("  closed")
            return True
        not_atomic = set(filter(lambda f: f.char, self.S))
        if self.S in self.old_S or not not_atomic:
            if verbose:
                print("  not closed")
            return False
        for f in not_atomic:
            if verbose:
                print(f)
            s, c = f.solve()
            if len(c) == 1:
                new_S = self.S - {f}
                if TableauxINT(new_S | s[0],
                               certain=c[0]).solve(verbose=verbose):
                    return True
            else:
                all_t = True
                for i in range(len(s)):
                    new_S = self.S - {f}
                    if not TableauxINT(new_S | s[i],
                                       certain=c[i]).solve(verbose=verbose):
                        all_t = False
                        break
                return all_t


if __name__ == "__main__":
    f = If(["A", "B", "A", "A", "B", "B"])
    print(f)
    print(TableauxCL([f]).solve(verbose=True))
    print("\n\n")

    f = Or(["A", Not(["A"])])
    print(f)
    print(TableauxCL([f]).solve(verbose=True))
    print("\n\n")

    f = Et(["A", Not(["A"])])
    print(f)
    print(TableauxCL([f]).solve(verbose=True))
    print("\n\n")

    f = If([
        Et([
            Or(["P", "Q"]),
            If(["P", "R"]),
            Et([
                Not(["P"]),
                If(["Q", "R"])])]),
        "R"])
    print(f)
    print(TableauxCL([f]).solve(verbose=True))
    print("\n\n")
