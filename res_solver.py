def resolution_solver(clauses):
    clauses = [set(c) for c in clauses]
    if set() in clauses:
        return False
    new_clauses = True
    while new_clauses:
        new_clauses = False
        for Ci in clauses:
            for Cj in clauses:
                for l in Ci:
                    if -l in Cj:
                        resolvent = (Ci | Cj) - {l, -l}
                        if len(resolvent) == 0:
                            return False
                        if resolvent not in clauses:
                            clauses.append(resolvent)
                            new_clauses = True
    return True
