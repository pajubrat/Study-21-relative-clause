# Auxiliary functions used during certain processing steps

log_file = open('log.txt', 'w', encoding='utf-8')

def sWMcopy(sWM, SO):
    """
    This function copies syntactic objects in sWM and SO
    and updates internal links (adjuncts, chains, copy-links)
    """
    sWM2 = [x.copy() for x in sWM if x not in set(SO)]
    SO2 = [x.copy() for x in SO]
    # Updates internal links
    for x in sWM2 + SO2:
        update_links(x)
    return set(sWM2), tuple(SO2)

def update_links(X):
    """
    Updates internal links inside syntactic object X
    'X.isomapping' points to the copied constituent. Thus, X.mother.isomapping
    refers to constituent Y that was created from X.mother. In this function
    we assume that X.mother/X.adjuncts for adjuncts and X.copied (internal link)
    still point to the source constituent and must be updated, which is what
    this function does.
    """
    if X.adjunct:
        X.mother = X.mother.isomapping
    if X.adjuncts:
        X.adjuncts = {x.isomapping for x in X.adjuncts if x}
    if X.copied:
        X.copied = X.copied.isomapping
    if not X.zero_level():
        update_links(X.left())
        update_links(X.right())


def tset(X):
    """
    Type conversion
    """
    if isinstance(X, set):
        return X
    else:
        return {X}


def print_lst(lst):
    return ', '.join([f'{x}' for x in lst])


def print_constituent_lst(sWM):
    stri = f'{print_ordered_lst([x for x in sWM if not x.adjunct])}'
    if [x for x in sWM if x.adjunct]:
        stri += f' | {print_adjunct_lst([x for x in sWM if x.adjunct])}'
    return stri


def print_adjunct_lst(lst):
    return ', '.join(sorted([f'{x}(:{x.mother.head().lexical_category()})' for x in lst], key=str.casefold, reverse=True))


def print_ordered_lst(lst):
    return ', '.join(sorted([f'{x}' for x in lst], key=str.casefold, reverse=True))

