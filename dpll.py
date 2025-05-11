def dpll(clauses, assignment=None):
    if assignment is None:
        assignment = {}
    clauses = [set(c) for c in clauses]
    changed = True
    while changed:
        changed = False
        for c in clauses:
            if len(c) == 0:
                return False
            if len(c) == 1:
                unit = next(iter(c))
                assignment[abs(unit)] = (unit > 0)
                new_clauses = []
                for d in clauses:
                    if unit in d:
                        continue
                    if -unit in d:
                        d = d.copy()
                        d.remove(-unit)
                    new_clauses.append(d)
                clauses = new_clauses
                changed = True
                break
    all_literals = {lit for c in clauses for lit in c}
    for lit in list(all_literals):
        if -lit not in all_literals:
            assignment[abs(lit)] = (lit > 0)
            clauses = [c for c in clauses if lit not in c]
            all_literals = {lit for c in clauses for lit in c}
    if not clauses:
        return True
    first_clause = clauses[0]
    lit = next(iter(first_clause))
    new_clauses = [c.copy() for c in clauses] + [{lit}]
    if dpll(new_clauses, assignment.copy()):
        return True
    new_clauses = [c.copy() for c in clauses] + [{-lit}]
    return dpll(new_clauses, assignment.copy())
