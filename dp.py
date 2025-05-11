def unit_propagate(clauses):
    assignment = {}
    changed = True
    while changed:
        changed = False
        for c in clauses:
            if len(c) == 0:
                return None
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
    return clauses, assignment

def pure_literal_assign(clauses):
    assignment = {}
    all_literals = {lit for c in clauses for lit in c}
    for lit in list(all_literals):
        if -lit not in all_literals:
            assignment[abs(lit)] = (lit > 0)
            clauses = [c for c in clauses if lit not in c]
            all_literals = {lit for c in clauses for lit in c}
    return clauses, assignment

def dp_solver(clauses):
    clauses = [set(c) for c in clauses]
    result = unit_propagate(clauses)
    if result is None:
        return False
    clauses, _ = result

    clauses, _ = pure_literal_assign(clauses)
    if not clauses:
        return True

    all_lits = {lit for c in clauses for lit in c}
    pivot = None
    for lit in all_lits:
        if -lit in all_lits:
            pivot = abs(lit)
            break
    if pivot is None:
        return True

    pos_clauses = [c for c in clauses if pivot in c]
    neg_clauses = [c for c in clauses if -pivot in c]
    other_clauses = [c for c in clauses if pivot not in c and -pivot not in c]
    new_clauses = []
    for c in pos_clauses:
        for d in neg_clauses:
            resolvent = (c | d) - {pivot, -pivot}
            if len(resolvent) == 0:
                return False
            new_clauses.append(resolvent)

    new_formula = other_clauses + new_clauses
    return dp_solver(new_formula)

