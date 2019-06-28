ET_CHAR = "∧"
OR_CHAR = "∨"
IF_CHAR = "→"
NOT_CHAR = "¬"
THEOREM_CHAR = "⊢"
NOT_THEOREM_CHAR = "⊬"


class FBF:
    # The Well Formulated Formula, eventually annotated with a sign
    def __str__(self):
        txt = self.sign if self.sign else ""
        if len(self.args) > 1 and self.char:
            fbf1 = "({})".format(self.args[0].str_wo_sign()) \
                if self.args[0].char \
                else self.args[0].str_wo_sign()
            if len(self.args[0].args) > 1 and fbf1[0] != "(":
                fbf1 = "(" + fbf1 + ")"
            fbf2 = "({})".format(self.args[1].str_wo_sign()) \
                if self.args[1].char \
                else self.args[1].str_wo_sign()
            if len(self.args[1].args) > 1 and fbf2[0] != "(":
                fbf2 = "(" + fbf2 + ")"
            txt += "{} {} {}".format(fbf1, self.char, fbf2)
        elif self.char:
            fbf = "({})".format(self.args[0].str_wo_sign()) \
                if self.args[0].char \
                else self.args[0].str_wo_sign()
            if len(self.args[0].args) > 1 and fbf[0] != "(":
                fbf = "(" + fbf + ")"
            txt += "{}{}".format(self.char, fbf)
        else:
            txt += self.args
        return txt

    def str_wo_sign(self):
        if len(self.args) > 1 and self.char:
            fbf1 = "({})".format(self.args[0].str_wo_sign()) \
                if self.args[0].char \
                else self.args[0].str_wo_sign()
            if len(self.args[0].args) > 1 and fbf1[0] != "(":
                fbf1 = "(" + fbf1 + ")"
            fbf2 = "({})".format(self.args[1].str_wo_sign()) \
                if self.args[1].char \
                else self.args[1].str_wo_sign()
            if len(self.args[1].args) > 1 and fbf2[0] != "(":
                fbf2 = "(" + fbf2 + ")"
            return "{} {} {}".format(fbf1, self.char, fbf2)
        elif self.char:
            fbf = "({})".format(self.args[0].str_wo_sign()) \
                if self.args[0].char \
                else self.args[0].str_wo_sign()
            if len(self.args[0].args) > 1 and fbf[0] != "(":
                fbf = "(" + fbf + ")"
            return "{}{}".format(self.char, fbf)
        else:
            return self.args

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
    def __init__(self, *args, sign=None):
        "The logical et connector"
        self.char = ET_CHAR
        self.sign = sign
        self.args = list(map(lambda a: Atom(a) if isinstance(a, str) else a,
                             args))
        self.solver = "CL"
        if len(self.args) < 2:
            raise Exception("Object is not a valid formula")
        elif len(self.args) > 2:
            self = self.__init__(Et(*args[0:2]), *args[2:])

    def solve(self, solver):
        # just check a tableaux table
        fbf1, fbf2 = self.args
        if solver == "CL":
            if self.sign == "T":
                fbf1.sign = "T"
                fbf2.sign = "T"
                return [{fbf1, fbf2}]
            elif self.sign == "F":
                fbf1.sign = "F"
                fbf2.sign = "F"
                return [{fbf1}, {fbf2}]
        elif solver == "INT":
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
    def __init__(self, *args, sign=None):
        "The logical Or connector"
        self.char = OR_CHAR
        self.sign = sign
        self.args = list(map(lambda a: Atom(a) if isinstance(a, str) else a,
                             args))
        if len(self.args) < 2:
            raise Exception("Object is not a valid formula")
        elif len(self.args) > 2:
            self = self.__init__(Or(*args[0:2]), *args[2:])

    def solve(self, solver):
        fbf1, fbf2 = self.args
        if solver == "CL":
            if self.sign == "T":
                fbf1.sign = "T"
                fbf2.sign = "T"
                return [{fbf1}, {fbf2}]
            elif self.sign == "F":
                fbf1.sign = "F"
                fbf2.sign = "F"
                return [{fbf1, fbf2}]
        elif solver == "INT":
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
    def __init__(self, *args, sign=None):
        "The logical if connector"
        self.char = IF_CHAR
        self.sign = sign
        self.args = list(map(lambda a: Atom(a) if isinstance(a, str) else a,
                             args))
        if len(self.args) < 2:
            raise Exception("Object is not a valid formula")
        elif len(self.args) > 2:
            self = self.__init__(If(*args[0:2]), *args[2:])

    def solve(self, solver):
        fbf1, fbf2 = self.args
        if solver == "CL":
            if self.sign == "T":
                fbf1.sign = "F"
                fbf2.sign = "T"
                return [{fbf1}, {fbf2}]
            else:
                fbf1.sign = "T"
                fbf2.sign = "F"
                return [{fbf1, fbf2}]
        if solver == "INT":
            if self.sign == "T":
                if not fbf1.char:
                    fbf1.sign = "F"
                    fbf2.sign = "T"
                    return [{fbf1}, {fbf2}], [False, False]
                elif fbf1.char == ET_CHAR:
                    fbf = If(fbf1.args[0],
                             If(fbf1.args[1], fbf2),
                             sign="T")
                    return [{fbf}], [False]
                elif fbf1.char == OR_CHAR:
                    fbf1_new = If(fbf1.args[0], fbf2, sign="T")
                    fbf2_new = If(fbf1.args[1], fbf2, sign="T")
                    return [{fbf1_new, fbf2_new}], [False]
                # elif fbf1.char == IF_CHAR:
                #     fbf1.sign = "T"
                #     fbf_new = If(fbf1.args[1], fbf2, sign="F")
                #     fbf2.sign = "T"
                #     return [{fbf1, fbf_new}, {fbf2}], [False, False]
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
    def __init__(self, *args, sign=None):
        "The logical not operator"
        self.char = NOT_CHAR
        self.sign = sign
        self.args = list(map(lambda a: Atom(a) if isinstance(a, str) else a,
                             args))
        if len(self.args) != 1:
            raise Exception("Object is not a valid formula")

    def solve(self, solver):
        fbf = self.args[0]
        if solver == "CL":
            fbf.sign = "F" if self.sign == "T" else "T"
            return [{fbf}]
        elif solver == "INT":
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

    def is_closed(self):
        for fbf in self.S:
            if any(map(lambda f: fbf.closed(f), self.S - {fbf})):
                return True
        return False


class TableauxCL(Tableaux):
    def __init__(self, S):
        super().__init__(S, "CL")

    def apply_formula_to(self):
        "Get the most convenient formula to apply the rule"
        # those are rules that split the tableaux:
        # there are not convenient
        splits = {"T" + OR_CHAR,
                  "T" + IF_CHAR,
                  "F" + ET_CHAR}
        not_atomic = set(filter(lambda f: f.char, self.S))
        if not not_atomic:
            return None
        # get all not atomic formulas that do not split the tableaux
        not_split_rules = set(filter(lambda f: f.sign + f.char not in splits,
                                     not_atomic))
        # if any, get one randomly, else get one randomly
        s = not_split_rules.pop() if not_split_rules else not_atomic.pop()
        # and remove it from S
        self.S -= {s}
        return s

    def solve(self, verbose=False):
        if verbose:
            print(", ".join([str(fbf) for fbf in self.S]))
        # check if the tableaux is closed
        if self.is_closed():
            if verbose:
                print(" closed " + "-"*11)
            return True
        # if not, get a formula to apply the rule
        fbf = self.apply_formula_to()
        # if there are no formula, the tableaux can not be closed
        if not fbf:
            if verbose:
                print(" not closed " + "-"*7)
            return False
        if verbose:
            print(" {}{} ".format(fbf.sign, fbf.char) + "-"*15)
        s = fbf.solve(self.solver)
        # add the solution to S
        if len(s) == 1:
            self.S |= s[0]
        else:
            # if it splits the tableaux, both branches must be closed
            return all([TableauxCL(list(self.S | t)).solve(verbose=verbose)
                        for t in s])
        # repeat recoursively until the solution
        return self.solve(verbose=verbose)


class TableauxINT(Tableaux):
    def __init__(self, S, old_S=list()):
        super().__init__(S, "INT")
        # get all certain formula
        self.Sc = set(filter(lambda f: f.sign in {"T", "Fc"},
                             self.S))
        # to check if the recoursive algorithm enters in a loop
        self.old_S = old_S

    def solve(self, verbose=False):
        # check if the tableaux is closed
        if self.is_closed():
            if verbose:
                print(" closed " + "-"*11)
                print(", ".join([str(s) for s in self.S]))
            return True
        # get all formulas which a rule can be applied to
        not_atomic = set(filter(lambda f: f.char, self.S))
        # if any, the tableaux is open
        if self.S in self.old_S or not not_atomic:
            return False
        # check if exists a sequence of formulas that closed the tableaux
        # with an exploratory algorithm: it checks all possible sequences
        for fbf in not_atomic:
            fbf = fbf
            s, c = fbf.solve(self.solver)
            # if a sequence is correct, this is the solution
            if all([TableauxINT(list(((self.Sc if c[i] else
                                       self.S) - {fbf}) | s[i]),
                                old_S=self.old_S +
                                [self.S]).solve(
                                    verbose=verbose)
                    for i in range(len(s))]):
                if verbose:
                    print(" {}{} ".format(fbf.sign, fbf.char) +
                          "-"*(16 - len(fbf.sign)))
                    print(", ".join([str(s) for s in self.S]))
                return True
        # if all combinations are tested, the tableaux is open
        return False


def is_theorem(formula, logic, verbose=False):
    "Check if a formula is a theorem in a logic"
    if logic == "CL":
        return TableauxCL([formula]).solve(verbose)
    elif logic == "INT":
        return TableauxINT([formula]).solve(verbose)
    else:
        return None


def solve(formula, verbose=False, logic=["CL", "INT"]):
    "Solve the formula the result"
    txt = str(formula)
    results = {l: is_theorem(formula, l, verbose)
               for l in logic}
    for l, r in results.items():
        print(l + " "*(5 - len(l)) + (THEOREM_CHAR if r
                                      else NOT_THEOREM_CHAR) + "  " + txt)
    print("")
    return results


if __name__ == "__main__":
    solve(If("A", "B", "A", "A", "B", "B"))
    solve(Or("A", Not("A")))
    solve(Not(Not(Or("A", Not("A")))))
    solve(Et("A", Not("A")))
    solve(Not(Et("A", Not("A"))))
    solve(If(
        Et(
            Or("P", "Q"),
            If("P", "R"),
            Et(
                Not("P"),
                If("Q", "R"))),
        "R"))
    solve(If(Or("A", Not("A")),
             "B", Not(Not("B"))))
    solve(If("A", Not(Not("A"))))
    solve(If(Not(Not("A")), "A"))
    solve(If(Not(Not((Not("A")))), Not("A")))
