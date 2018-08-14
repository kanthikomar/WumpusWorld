import time
from copy import copy
from logical_exp import *

def main(argv):
    model_dict = dict()
    if len(argv) != 4:
        print('Usage: %s [wumpus-rules-file] [additional-knowledge-file] [input_file]' % argv[0])
        sys.exit(0)
    try:
        input_file = open(argv[1], 'rb')
    except:
        print('failed to open file %s' % argv[1])
        sys.exit(0)
    print '\nLoading wumpus rules...'
    knowledge_base = logical_exp()
    knowledge_base.connective = ['and']
    for line in input_file:
        if line[0] == '#' or line == '\r\n' or line == '\n' or line == '\r':
            continue
        counter = [0]
        subexpression = read_expression(line.rstrip('\r\n'), counter)
        knowledge_base.subexpressions.append(subexpression)
    input_file.close()
    try:
        input_file = open(argv[2], 'rb')
    except:
        print('failed to open file %s' % argv[2])
        sys.exit(0)
    print 'Loading additional knowledge...'
    for line in input_file:
        if line[0] == '#' or line == '\r\n' or line == '\n' or line == '\r':
            continue
        counter = [0]
        subexpression = read_expression(line.rstrip('\r\n'), counter)
        knowledge_base.subexpressions.append(subexpression)
    input_file.close()
    if not valid_expression(knowledge_base):
        sys.exit('invalid knowledge base')
    try:
        input_file = open(argv[3], 'rb')
    except:
        print('failed to open file %s' % argv[3])
        sys.exit(0)
    print 'Loading statement...'
    input_statement = input_file.readline().rstrip('\r\n')
    input_file.close()
    counter = [0]
    statement = read_expression(input_statement, counter)
    if not valid_expression(statement):
        sys.exit('invalid statement')
##################################################################
    negative_statement = '(not %s)' %(input_statement) 
    counter = [0]
    neg_statement = read_expression(negative_statement, counter)
    if not valid_expression(neg_statement):
        sys.exit('Negative of the statment is invalid')
    knowledge=get_symbols(knowledge_base)    ########################## 
    knowledge=knowledge+get_symbols(statement)
    symbols=set(knowledge)

    for subexp in knowledge_base.subexpressions:    ############## Updating model with the truth values
        if subexp.connective[0] == '':
            symbol = subexp.symbol
            model_dict[symbol[0]] = True
            symbols.discard(symbol[0])
        elif subexp.connective[0] == 'not':
            symbol = subexp.subexpressions[0].symbol
            model_dict[symbol[0]] = False
            symbols.discard(symbol[0])

    print '\nChecking emtailement of the statement with KB: ',
    print_expression(statement, '')
    time1 = time.time()
    if_true  = tt_check_all(knowledge_base,statement,list(symbols),model_dict)  ### TT_entail for given statement
    if_false = tt_check_all(knowledge_base,neg_statement,list(symbols),model_dict) ## TT_entail for negation of the statement
    time2 = time.time()
    print '\ntime required to check entailment:', (time2-time1)
    file_writer = open('result.txt','w')
    if if_true and not(if_false):
        print " is definitely true"
        file_writer.write('definitely true')
    if if_false and not(if_true):
        print " is definitely false"
        file_writer.write('definitely false')
    if (not if_true) and (not if_false):
        print " is possibly true possibly false"
        file_writer.write('possibly true, possibly false')
    if if_true and if_false:
        print " is true as well as false"
        file_writer.write('both true and false')
    file_writer.close()

def get_symbols(smt):
    list = []
    if smt.symbol[0]:
        list.append(smt.symbol[0])
    else:
        for subexp in smt.subexpressions:
            list = list + get_symbols(subexp)
    return list

def tt_check_all(knowledge_base, statement, symbols, model):    ##### check entailment against the model i.e kb + additional kb provided
    if len(symbols) == 0:
        if pl_true(knowledge_base, model):
            return pl_true(statement, model)
        else:
            return True
    else:
        firstsym = symbols.pop()
        temp = tt_check_all(knowledge_base, statement, copy(symbols), extend(firstsym,True, copy(model))) and \
               tt_check_all(knowledge_base, statement, copy(symbols), extend(firstsym,False, copy(model)))
        return temp

def pl_true(smt, model_dict):       ############################ Checking truth value of statements
    truth_value = None
    if smt.symbol[0] != '' and smt.connective[0] == '':
        truth_value = model_dict[smt.symbol[0]]

    elif smt.connective[0] == 'not':
        truth_value = not (pl_true(smt.subexpressions[0], model_dict))

    elif smt.connective[0] == 'if':
        truth_value = (not pl_true(smt.subexpressions[0],model_dict)) or pl_true(smt.subexpressions[1],model_dict)

    elif smt.connective[0] == 'iff':
        truth_value = pl_true(smt.subexpressions[0],model_dict) == pl_true(smt.subexpressions[1],model_dict)

    elif smt.connective[0] == 'or':
        truth_value = False
        list = []
        for sub in smt.subexpressions:
            list.append(pl_true(sub,model_dict))
        for tlist in list:
            truth_value = truth_value or tlist

    elif smt.connective[0] == 'xor':
        truth_value = False
        list = []
        for sub in smt.subexpressions:
            list.append(pl_true(sub,model_dict))
        for r in list:
            truth_value = truth_value != r
    elif smt.connective[0] == 'and':
        truth_value = True
        list = []
        for sub in smt.subexpressions:
            list.append(pl_true(sub,model_dict))
        for tlist in list:
            truth_value = truth_value and tlist

    return truth_value

def extend(symbol, value, model):
    model[symbol] = value
    return model

if __name__ == '__main__':
    main(sys.argv)