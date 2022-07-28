#include <utility>
#include <map>
#include <vector>
#include <sstream>
#include <iostream>
#include <memory>
using namespace std;

class Parse {
    public:
    string prod;
	vector<string> tokens;
	vector< shared_ptr<Parse> > children;
};
map<string, pair<vector<string>, map<string,pair<string,int> > > > table;
map<string, int> stack;
int bb = 0;
int curr_offset = 0;
string procedure="";
string signature_match = "";
string a = "procedure INT ID LPAREN params RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE";
string h = "main INT WAIN LPAREN dcl COMMA dcl RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE";
int curr_index = 0;
int param_counter = 0;
static const size_t poss = -1;

bool terminal(string word) {
  string terminal_sym[] = {
    "BOF", "BECOMES", "COMMA", "ELSE", "EOF", "EQ", 
    "GE", "GT", "ID", "IF", "INT", "LBRACE", "LE", "LPAREN", "LT", "MINUS", "NE", 
    "NUM", "PCT", "PLUS", "PRINTLN", "RBRACE", "RETURN", "RPAREN", "SEMI", "SLASH", "STAR", 
    "WAIN", "WHILE", "AMP", "LBRACK", "RBRACK", "NEW", "DELETE", "NULL"
    };
    for(int i = 0; i < 35; i++){
        if(word == terminal_sym[i]) {
            return true;
        }
    }
    return false;
}

void make_tree(vector< shared_ptr<Parse> > &nodes, shared_ptr<Parse> parse){
	int child_count=0;
	if (!terminal(parse->tokens.at(0))) {
        child_count = parse->tokens.size() - 1;
	}
	else {
		child_count = 0;
	}
 	if (child_count) {
         for (int i = 1; i <= child_count; i++) {
 		    parse->children.push_back(nodes.at(++curr_index)); 
 		    make_tree(nodes, nodes.at(curr_index));
 	    }
    }
 	return;
}

void tokenize(const string &line, vector<string> &tokens){
	stringstream ss (line);
	string tk;
	while (ss >> tk) {
		tokens.push_back(tk);
	}
}

string find_at(shared_ptr<Parse> parse, int a, int b){
    string result=parse->children.at(a)->tokens.at(b);
    return result;
}

void make_table(shared_ptr<Parse> parse, bool &error_check) {
    string b = "paramlist dcl";
    string c = "type INT STAR";
    string d = "type INT";
    string e = "paramlist dcl COMMA paramlist";
    string f = "factor ID LPAREN arglist RPAREN";
    string g = "factor ID";
    string j = "dcl type ID";
	if (parse->prod == j) {
        string name = find_at(parse, 1, 1);
		string w = parse->children.at(0)->prod;
		if (w == c) {
			w = "int*";
		}
		else if (w == d) {
			w = "int";
		}
		if(table[procedure].second.find(name) != table[procedure].second.end()) {
			cerr << "ERROR, more than one decleration found" << endl;
            error_check=true;
            return;
		}
		else { 
			table[procedure].second[name].first = w;
            table[procedure].second[name].second = curr_offset;
            curr_offset -= 4;
		}
	}
	else if (parse->prod == h || parse->prod == a) {
        string nn = find_at(parse, 1, 1);
		if (table.find(nn) != table.end()) {
			cerr << "ERROR, more than one decleration found" << endl;
            error_check=true;
            return;
		}
		else {
			vector<string> signature; 
			map<string, pair<string, int> > new_sym;
			pair<vector<string>, map<string, pair<string, int> > > new_table (signature,new_sym);
			table[nn] = new_table;
			procedure = nn;
            curr_offset=0;
		}
        if (parse->prod == h) {
			string sigp = parse->children.at(3)->children.at(0)->prod;
			string sigp5 = parse->children.at(5)->children.at(0)->prod;
			if (sigp == c) {
				sigp = "int*";
			}
            if (sigp5 == c) {
				sigp5 = "int*";
			}
			if (sigp == d) {
				sigp = "int";
			}	
			if (sigp5 == d) {
				sigp5 = "int";
            }
			table["wain"].first.push_back(sigp);
			table["wain"].first.push_back(sigp5);
		}
	}
    else if (parse->prod == f) {
        string nn = find_at(parse, 0, 1);
		if (table.find(nn) == table.end()) {
			cerr << "ERROR, no decleration found" << endl;
            error_check=true;
            return;
		}
		else if (table[procedure].second.find(nn) != table[procedure].second.end()) {
			cerr << "ERROR, declared as both precuder and variable" << endl;
            error_check=true;
            return;
		}
	} 
    else if (parse->prod == g) {
		string kk = find_at(parse, 0, 1);
		if (table[procedure].second.find(kk) == table[procedure].second.end()){
			cerr << "ERROR, no decleration found but used" << endl;
            error_check=true;
            return;
		}
	}
    else if (parse->prod == "lvalue ID") {
		string kk = find_at(parse, 0, 1);
		if (table[procedure].second.find(kk) == table[procedure].second.end()){
			cerr << "ERROR, no decleration found but used" << endl;
            error_check=true;
            return;
		}
    }
	else if (parse->prod == f) {
		string nn = find_at(parse, 0, 1);
		if (table.find(nn) == table.end()) {
			cerr << "ERROR, no decleration found but used for precuder" << endl;
            error_check=true;
            return;
		}
		else if (table[procedure].second.find(nn) != table[procedure].second.end()){
			cerr << "ERROR, declared as both precuder and variable" << endl;
            error_check=true;
            return;
		}
	}
    else if (parse->prod == "factor ID LPAREN RPAREN") {
		string nn = find_at(parse, 0, 1);
		if (table.find(nn) == table.end()) {
			cerr << "ERROR, no decleration found but used for precuder" << endl;
            error_check=true;
            return;
		}
		else if (table[procedure].second.find(nn) != table[procedure].second.end()) {
			cerr << "ERROR, declared as both precuder and variable" << endl;
            error_check=true;
            return;
		}
	}
    else if (parse->prod == b) {
		string prod2 = parse->children.at(0)->children.at(0)->prod;
		if (prod2 == c) {
			prod2 = "int*";
		}
		else if (prod2 == d){
			prod2 = "int";
		}
		table[procedure].first.push_back(prod2);
	}

    else if (parse->prod == e){
		string prod2 = parse->children.at(0)->children.at(0)->prod;
		if (prod2 == c){
			prod2 = "int*";
		}
		else if (prod2 == d){
			prod2 = "int";
		}
		table[procedure].first.push_back(prod2);
	}
	for (vector< shared_ptr<Parse> >::iterator it = parse->children.begin(); it != parse->children.end(); it++) {
		make_table(*it, error_check);
	}
}



string type_func(shared_ptr<Parse> parse) {
    if(parse->tokens[0] == "NUM") {
        return "int";
    }
    else if(parse->tokens[0] == "NULL") {
        return "int*";
    }

    
     else if(parse->tokens[0] == "ID"){
        return table[procedure].second[parse->tokens[1]].first;
    } 
    
    else if (parse->prod == "factor NUM" ||  parse->prod == "factor NULL") {
        return type_func(parse->children.at(0));
    }

    else if (parse->prod == "lvalue ID" || parse->prod == "term factor" || 
     parse->prod == "factor ID" || parse->prod == "expr term"){
        return type_func(parse->children.at(0));
    }
    
    else if(parse->prod== "factor LPAREN expr RPAREN" || parse->prod == "lvalue LPAREN lvalue RPAREN"){ 
        return type_func(parse->children.at(1));
    }
    
    else if(parse->prod == "factor AMP lvalue"){ //
        if(type_func(parse->children.at(1)) == "int"){
            // error_check=true;
            return "int*";
        } else {
            return "ERROR, address/ampersent error";
        }
    } 

    else if(parse->prod == "lvalue STAR factor" || parse->prod == "factor STAR factor"){ ///correct
        if(type_func(parse->children.at(1)) == "int*"){
            //error_check=true;
            return "int";
        } else {
            return "ERROR, pointer";
        }
    } 
    
    else if(parse->prod == "factor NEW INT LBRACK expr RBRACK"){ // correct
        if(type_func(parse->children.at(3)) == "int"){
            //error_check=true;
            return "int*";
            //return "ERROR, new int[] array error";
        } else {
            return "ERROR, new int[] array error"; 
            //return "int*";
        }
    } 

    else if (parse->prod == "factor ID LPAREN RPAREN") { ///correct
		string nn = parse->children.at(0)->tokens.at(1);
		if (table.find(nn) == table.end()) {
			cerr << "ERROR, for factor ID" << endl;
		} else if (table[nn].first.size()) {
            cerr << "ERROR, wrong number of args for factor ID" << endl;
        }
		else {
            return "int";
		}
	}

    else if(parse->prod == "main INT WAIN LPAREN dcl COMMA dcl RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE"){ ////
        //cout << "hello" << endl;
        if (parse->children.at(5)->children.at(0)->prod == "type INT" && type_func(parse->children.at(11)) == "int") {
            return "X";
        } else {
            return "ERROR, wain arg is not int";
        }
    } 
    
     else if(parse->prod == "dcls dcls dcl BECOMES NULL SEMI") { ///corect
        if(parse->children.at(1)->children.at(0)->prod == "type INT STAR") {
            return "X";
        } else {
            return "ERROR, int to null is illegal";
        }
    } 
    
    else if(parse->prod == "dcls dcls dcl BECOMES NUM SEMI" ) { ////correct
        if(parse->children.at(1)->children.at(0)->prod == "type INT") {
            return "X";
        } else {
            return "ERROR, NUM is illegal";
        }
    } 

    else if(parse->prod == "procedure INT ID LPAREN params RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE"){ ////
        if(type_func(parse->children.at(9)) == "int" && type_func(parse->children.at(7)) == "X" && type_func(parse->children.at(6)) == "X") {
            return "X";
        } else {
            return "ERROR, parameter for this function must be int";
        }
    } 

    else if(parse->prod == "test expr EQ expr" || parse->prod == "test expr NE expr" || 
    parse->prod == "test expr LT expr" || parse->prod == "test expr GT expr" || 
    parse->prod == "test expr GE expr" || parse->prod == "test expr LE expr"){
        if (type_func(parse->children.at(0)) == type_func(parse->children.at(2))) {
            return "X";
        }
        else {
            return "ERROR, wrong test type";
        }
    }

    else if(parse->prod == "DELETE LBRACK RBRACK expr SEMI"){
        if(type_func(parse->children.at(2)) != "int*"){
            //error_check=true;
            return "ERROR, delete pointer";
        }
    } 
    
    
    else if(parse->prod == "statement lvalue BECOMES expr SEMI") { ///
        if(type_func(parse->children.at(0)) == type_func(parse->children.at(2))){
            // error_check=true;
            return "X";
            //return "ERROR, wrong type";
        } else {
            return "ERROR, wrong type 1";
        }
    } 
    
    else if(parse->prod == "statement PRINTLN LPAREN expr RPAREN SEMI"){ ///
        //cout << type_func(parse->children.at(2)) << endl;
        if(type_func(parse->children.at(2)) == "int"){
            // error_check=true;
            return "X";
            //return "ERROR, wrong type must be int";
        } else {
            return "ERROR, wrong type must be int";
        }
    } else if (parse->prod == "statements") { ///
		return "X";
	}
    
     else if (parse->prod == "dcls") { ///
		return "X";
	} 
    
    else if(parse->prod == "statement DELETE LBRACK RBRACK expr SEMI"){ /////
        if(type_func(parse->children.at(3)) == "int*") {
            return "X";
        } else {
            return "ERROR, wrong type cannot be pointer";
        }
    } 
    
    
    else if(parse->prod == "PRINTLN LPAREN expr RPAREN SEMI"){
        if(type_func(parse->children.at(1)) == "int"){
            //error_check=true;
            return "X";
        } else {
            return "ERROR, println argument must be int";
        }
    } 
    
    else if(parse->prod == "expr expr PLUS term"){
        if(type_func(parse->children.at(0)) == "int" && type_func(parse->children.at(2)) == "int"){
            return "int";
        } else if(type_func(parse->children.at(0)) == "int*" && type_func(parse->children.at(2)) == "int") {
            return "int*";
        } else if(type_func(parse->children.at(0)) == "int" && type_func(parse->children.at(2)) == "int*") {
            return "int*";
        } else {
            return "ERROR, two pointers addition not allowed";
        }
    } 
    
    else if(parse->prod == "expr expr MINUS term"){
        if(type_func(parse->children.at(0)) == "int" && type_func(parse->children.at(2)) == "int"){
            return "int";
        } else if(type_func(parse->children.at(0)) == "int*" && type_func(parse->children.at(2)) == "int") {
            return "int*";
        } else if(type_func(parse->children.at(0)) == "int*" && type_func(parse->children.at(2)) == "int*") {
            return "int";
        } else {
            return "ERROR, pointer minus not allowed";
        }
    }
    

    else if(parse->prod == "factor ID LPAREN arglist RPAREN"){
        vector<string> proc_check;
        proc_check.push_back(type_func(parse->children.at(2)->children.at(0)));
        shared_ptr<Parse> node = parse->children.at(2);
        while (node->children.size() > 1) {
            node = node->children.at(2);
            proc_check.push_back(type_func(node->children.at(0)));
        }
        string x = parse->children.at(0)->tokens.at(1);
        if (proc_check.size() != table[x].first.size()) {
            return "ERROR, size";
        }
        for (int i = 0; i < proc_check.size(); ++i) {
            
            if (proc_check[i] != table[x].first.at(i)) {
                cout << proc_check[i] << "proc_check i " << endl;
                return "ERROR, not match";
            }
        }
        return "int";
    }
    
    else if(parse->prod == "term term STAR factor" || parse->prod == "term term PCT factor" || parse->prod == "term term SLASH factor"){
        if(type_func(parse->children.at(0)) == "int" && type_func(parse->children.at(2)) == "int") {
            return "int";
        } else {
            return "ERROR, cannot multiply";
        }
    }
    return "none";
}

bool valid_type(shared_ptr<Parse> parse){
  for(vector< shared_ptr<Parse> >::iterator it=parse->children.begin(); it!=parse->children.end(); ++it) {    
    if((*it)->prod == "main INT WAIN LPAREN dcl COMMA dcl RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE"){
      procedure = "wain";
      if ((*it)->children.at(5)->children.at(0)->prod != "type INT" || type_func((*it)->children.at(11)) != "int") {
        cerr << "ERROR, wain arg is not int" << endl;
    }
    }
    else if((*it)->prod == "procedure INT ID LPAREN params RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE"){
      procedure = (*it)->children.at(1)->tokens.at(1);
      if (type_func((*it)->children.at(9)) != "int") {
          cerr << "ERROR,return is not int" << endl;
      }
    } else if(type_func(*it).find("ERROR") != poss){
        cerr << type_func(*it) << endl;
        return false;
    }
    valid_type(*it);
  }
  return true;
}

void push(int p) {
    cout << "sw $" << p << ", -4($30)" << endl;
    cout << "sub $30, $30, $4" << endl;
}

void pop(int p) {
    cout << "lw $" << p << ", 0($30)" << endl;
    cout << "add $30, $30, $4" << endl;
}


//map<string, pair<vector<string>, map<string,pair<string,int> > > > table;
void generator(shared_ptr<Parse> parse) {
    if (parse->prod == "main INT WAIN LPAREN dcl COMMA dcl RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE") {
        cout << "sub $29, $30, $4" << endl;
        cout << "sw $1, -4($30)" << endl;
        cout << "sub $30, $30, $4" << endl;
        cout << "sw $2, -4($30)" << endl;
        cout << "sub $30, $30, $4" << endl;
        if (parse->children.at(3)->children.at(0)->prod == "type INT") {
            cout << "add $2, $0, $0" << endl;
        }
        push(31);
        cout << "lis $5" << endl;
        cout << ".word init" << endl;
        cout << "jalr $5" << endl;
        pop(31);
        generator(parse->children[8]);
        generator(parse->children[9]);
        generator(parse->children[11]);
    	cout << "add $30, $29, $4" << endl;
	    cout << "jr $31" << endl;
    } 
    else if(parse->prod == "start BOF procedures EOF" || parse->prod == "factor LPAREN expr RPAREN" ||
    parse->prod == "lvalue LPAREN lvalue RPAREN") { //
        generator(parse->children[1]);
    }
    else if (parse->prod == "dcls dcls dcl BECOMES NUM SEMI") {
		generator(parse->children[0]);
		cout << "lis $3" << endl;
        cout << ".word " << parse->children[3]->tokens[1] << endl;
        int offset = table[procedure].second[parse->children[1]->children[1]->tokens[1]].second;
		cout << "sw $3, " << offset << "($29)" << endl;
        cout << "sub $30, $30, $4" << endl;
	}
    else if(parse->prod == "dcls dcls dcl BECOMES NULL SEMI"){
    	generator(parse->children[0]);
		int offset = table[procedure].second[parse->children[1]->children[1]->tokens[1]].second;
        cout << "add $3, $0, $11" << endl;
    	cout << "sw $3, " << offset << "($29)" << endl;
        cout << "sub $30, $30, $4" << endl;
    }
    else if(parse->prod == "procedures main" || parse->prod == "term factor" 
    || parse->prod == "expr term") { //
        generator(parse->children[0]);
    }
    else if (parse->prod == "factor ID") { //
        string id = parse->children[0]->tokens[1];
        int offset = table[procedure].second[id].second;
        cout << "lw $3, " << offset << "($29)" << endl;
    }
    else if (parse->prod == "factor NUM") { //
        string no = parse->children[0]->tokens[1];
        cout << "lis $3" << endl;
        cout << ".word " << no << endl;
    }
    else if (parse->prod == "factor NULL") { //
		cout << "add $3, $0, $11" << endl;
	}
    else if(parse->prod == "statements") {
    }
    else if(parse->prod == "dcls") {
    }
    else if (parse->prod == "statements statements statement") { //
        generator(parse->children[0]);
        generator(parse->children[1]);
    }
    else if (parse->prod == "expr expr PLUS term") {//
        generator(parse->children[0]);
		push(3);
		generator(parse->children[2]);
		pop(5);
        if (type_func(parse->children[0]) == "int" && type_func(parse->children[2]) == "int") {
            cout << "add $3, $5, $3" << endl;
        } else if (type_func(parse->children[0]) == "int*" && type_func(parse->children[2]) == "int") {
            cout << "mult $3, $4" << endl;
            cout << "mflo $3" << endl;
            cout << "add $3, $5, $3" << endl;
        } else if (type_func(parse->children[0]) == "int" && type_func(parse->children[2]) == "int*") {
            cout << "mult $5, $4" << endl;
            cout << "mflo $5" << endl;
            cout << "add $3, $5, $3" << endl;
        }
    }
    else if (parse->prod == "expr expr MINUS term") {//
        generator(parse->children[0]);
		push(3);
		generator(parse->children[2]);
		pop(5);
        if (type_func(parse->children[0]) == "int" && type_func(parse->children[2]) == "int") {
            cout << "sub $3, $5, $3" << endl;
        } else if (type_func(parse->children[0]) == "int*" && type_func(parse->children[2]) == "int") {
            cout << "mult $3, $4" << endl;
            cout << "mflo $3" << endl;
            cout << "sub $3, $5, $3" << endl;
        } else if (type_func(parse->children[0]) == "int*" && type_func(parse->children[2]) == "int*") {
            cout << "sub $3, $5, $3" << endl;
            cout << "div $3, $4" << endl;
            cout << "mflo $3" << endl;
        }
    }
    else if (parse->prod == "term term STAR factor") {//
        generator(parse->children[0]);
		push(3);
		generator(parse->children[2]);
		pop(5);
        cout << "mult $3, $5" << endl;
		cout << "mflo $3" << endl;
    }
    else if (parse->prod == "term term SLASH factor") {//
        generator(parse->children[0]);
		push(3);
		generator(parse->children[2]);
		pop(5);
        cout << "div $5, $3" << endl;
		cout << "mflo $3" << endl;
    }
    else if (parse->prod == "term term PCT factor") {//
        generator(parse->children[0]);
		push(3);
		generator(parse->children[2]);
		pop(5);
        cout << "div $5, $3" << endl;
		cout << "mfhi $3" << endl;
    }
    else if (parse->prod == "statement lvalue BECOMES expr SEMI") {
        generator(parse->children[2]);
        push(3);
        generator(parse->children[0]);
        pop(5);
        cout << "sw $5, 0($3)" << endl;
    }
    else if(parse->prod == "lvalue ID"){
        cout << "lis $3" << endl;
        cout << ".word " << table[procedure].second[parse->children[0]->tokens[1]].second << endl;
        cout << "add $3, $29, $3" << endl;
    }
    else if(parse->prod == "statement WHILE LPAREN test RPAREN LBRACE statements RBRACE") {  
        ++bb;
		int u = bb;
        cout << "loop" << u << ":" << endl;
		generator(parse->children[2]);
		cout << "beq $3, $0, end" << u << endl;
		generator(parse->children[5]);
		cout << "beq $0, $0, loop" << u << endl;
        cout << "end" << u << ":" << endl;
    }
    else if (parse->prod == "statement PRINTLN LPAREN expr RPAREN SEMI") {
        generator(parse->children[2]);
		push(31);
		cout << "add $1, $3, $0" << endl;
        cout << "lis $5" << endl;
        cout << ".word print" << endl;
        cout << "jalr $5" << endl;
        cout << "lw $31, 0($30)" << endl;
        cout << "add $30, $30, $4" << endl;
	}
    else if (parse->prod == "test expr LT expr") {
        generator(parse->children[0]);
		push(3);
		generator(parse->children[2]);
		cout << "add $30, $30, $4" << endl;
        cout << "lw $5, -4($30)" << endl;
		if (type_func(parse->children[0]) == "int*") {
            cout << "sltu $3, $5, $3" << endl;
        } else if(type_func(parse->children[0]) == "int"){
		    cout << "slt $3, $5, $3" << endl;
        }
    }
    else if (parse->prod == "test expr EQ expr") {
        generator(parse->children[0]);
		push(3);
		generator(parse->children[2]);
        cout << "add $30, $30, $4" << endl;
        cout << "lw $5, -4($30)" << endl;
        if(type_func(parse->children[0]) == "int*") {
            cout << "sltu $6, $3, $5" << endl;
            cout << "sltu $7, $5, $3" << endl;
        } else if(type_func(parse->children[0]) == "int"){
            cout << "slt $6, $3, $5" << endl;
            cout << "slt $7, $5, $3" << endl;
        }
        cout << "add $3, $6, $7" << endl;
        cout << "sub $3, $11, $3" << endl;
    }
    else if (parse->prod == "test expr NE expr") {
        generator(parse->children[0]);
		push(3);
		generator(parse->children[2]);
		cout << "add $30, $30, $4" << endl;
        cout << "lw $5, -4($30)" << endl;
        if(type_func(parse->children[0]) == "int*") {
            cout << "sltu $6, $3, $5" << endl;
            cout << "sltu $7, $5, $3" << endl;
        } else if(type_func(parse->children[0]) == "int") {
            cout << "slt $6, $3, $5" << endl;
            cout << "slt $7, $5, $3" << endl;
        }
		cout << "add $3, $6, $7" << endl;
    }
    else if (parse->prod == "test expr LE expr") {
        generator(parse->children[0]);
        push(3);
		generator(parse->children[2]);
	    cout << "add $30, $30, $4" << endl;
        cout << "lw $5, -4($30)" << endl;
        if(type_func(parse->children[0]) == "int*") {
            cout << "sltu $3, $3, $5" << endl;
        } else if(type_func(parse->children[0]) == "int") {
            cout << "slt $3, $3, $5" << endl;
        }
		cout << "sub $3, $11, $3" << endl;
    }
    else if (parse->prod == "test expr GE expr") {
        generator(parse->children[0]);
        push(3);
		generator(parse->children[2]);
	    cout << "add $30, $30, $4" << endl;
        cout << "lw $5, -4($30)" << endl;
        if(type_func(parse->children[0]) == "int*") {
            cout << "sltu $3, $5, $3" << endl;
        } else if(type_func(parse->children[0]) == "int") {
            cout << "slt $3, $5, $3" << endl;
        }
		cout << "sub $3, $11, $3" << endl;
    }
    else if (parse->prod == "test expr GT expr") {
        generator(parse->children[0]);
        push(3);
		generator(parse->children[2]);
		cout << "add $30, $30, $4" << endl;
        cout << "lw $5, -4($30)" << endl;
        if(type_func(parse->children[0]) == "int*") {
            cout << "sltu $3, $3, $5" << endl;
        } else if(type_func(parse->children[0]) == "int") {
            cout << "slt $3, $3, $5" << endl;
        }
    }
    else if (parse->prod == "statement IF LPAREN test RPAREN LBRACE statements RBRACE ELSE LBRACE statements RBRACE") {
        ++bb;
		int ttt = bb;
		generator(parse->children[2]);
		cout << "beq $3, $0, else" << ttt << endl;
		generator(parse->children[5]);
		cout << "beq $0, $0, end" << ttt << endl;
		cout << "else" << ttt << ":" << endl;
		generator(parse->children[9]);
		cout << "end" << ttt << ":" << endl;
    }
    else if (parse->prod == "type INT STAR") { //
    }
    else if (parse->prod == "factor AMP lvalue"){ //
        generator(parse->children[1]);
    }
    else if (parse->prod == "lvalue STAR factor"){ //
        generator(parse->children[1]);
    }
    else if (parse->prod == "factor STAR factor"){ //
        generator(parse->children[1]);
        cout << "lw $3, 0($3)" << endl;
    }
    else if(parse->prod == "factor NEW INT LBRACK expr RBRACK") {
        generator(parse->children[3]);
		push(1);
		cout << "sub $1, $3, $0" << endl;
		push(31);
		cout << "lis $10" << endl;
        cout << ".word new" << endl;
        cout << "jalr $10" << endl;
		cout << "bne $3, $0, 1" << endl;
    	cout << "add $3, $0, $11" << endl;
		cout << "add $30, $30, $4" << endl;
        cout << "lw $31, -4($30)" << endl;
		cout << "add $30, $30, $4" << endl;
        cout << "lw $1, -4($30)" << endl;
    }
    else if (parse->prod == "statement DELETE LBRACK RBRACK expr SEMI") {
        generator(parse->children[3]);
        push(1);
		cout << "sub $1, $3, $0" << endl;
		push(31);
		cout << "beq $11, $1, 3" << endl;
		cout << "lis $10" << endl;
        cout << ".word delete" << endl;
        cout << "jalr $10" << endl;
        cout << "add $30, $30, $4" << endl;
        cout << "lw $31, -4($30)" << endl;
		cout << "add $30, $30, $4" << endl;
        cout << "lw $1, -4($30)" << endl;
    }
    else if (parse->prod == "procedures procedure procedures") { //
        generator(parse->children[1]);
        generator(parse->children[0]);
	}
    else if (parse->prod == "procedure INT ID LPAREN params RPAREN LBRACE dcls statements RETURN expr SEMI RBRACE") {
        procedure = parse->children[1]->tokens[1];
        //map<string, pair<vector<string>, map<string,pair<string,int> > > > table;
        if (parse->children[3]->prod == "params") { //
        }
        else if (parse->children[3]->prod == "params paramlist") {
			int new_arg = table[procedure].first.size();
            int new_val = new_arg * 4;
            for (map<string,pair<string,int> >::iterator it = table[procedure].second.begin(); it != table[procedure].second.end(); it++) {
                it->second.second += new_val;
            }
		}
        cout << "F" << procedure << ":" << endl;
        cout << "sub $29, $30, $4" << endl;
        generator(parse->children[6]);
        push(1);
        push(2);
        push(5);
        push(6);
        push(7);
        push(8);
        generator(parse->children[7]);
        generator(parse->children[9]);
        pop(8);
        pop(7);
        pop(6);
        pop(5);
        pop(2);
        pop(1);
        cout << "add $30, $29, $4" << endl;
		cout << "jr $31" << endl;
    }
    else if (parse->prod == "factor ID LPAREN RPAREN") { //
        push(29);
        push(31);
        cout << "lis $5" << endl;
        cout << ".word " << "F" << parse->children[0]->tokens[1] << endl;
        cout << "jalr $5" << endl;
        pop(31);
        pop(29);
    }
    else if (parse->prod == "factor ID LPAREN arglist RPAREN") {
        push(29);
        push(31);
        generator(parse->children[2]);
        cout << "lis $5" << endl;
        cout << ".word " << "F" << parse->children[0]->tokens[1] << endl;
        cout << "jalr $5" << endl;
		cout << "lis $5" << endl;
		cout << ".word " << table[parse->children[0]->tokens[1]].first.size() * 4 << endl;
        cout << "add $30, $30, $5" << endl;
        pop(31);
        pop(29);
	}
    else if(parse->prod =="arglist expr"){
        generator(parse->children[0]);
        push(3);
    }
    else if(parse->prod == "arglist expr COMMA arglist"){
        generator(parse->children[0]);
        push(3);
        generator(parse->children[2]);
    }
    /*else {
        for (int i = 0; i < parse->children.size(); ++i) {
            generator(parse->children[i]);
        }
    }*/
}


int main () {
	vector< shared_ptr<Parse> > nodes;
    bool error_check=false;
    string input;
	while (getline(cin,input)) {
        shared_ptr<Parse> ps (new Parse());
		ps->prod = input;
		tokenize(input, ps->tokens);
		nodes.push_back(ps);
	}
 	make_tree(nodes, nodes.at(0));
 	make_table(nodes.at(0), error_check);
    if (error_check) {
        return -1;
    } 
    valid_type(nodes.at(0));
    cout << "lis $4" << endl;
    cout << ".word 4" << endl;
    cout << "lis $11" << endl;
    cout << ".word 1" << endl;
    cout <<".import print" << endl;
    cout <<".import init" << endl;
    cout <<".import new" << endl;
    cout <<".import delete" << endl;
    //cout << "sub $29, $30, $4" << endl;
    generator(nodes.at(0));
    int mv = table["wain"].second.size();
    mv *= 4;
 	return 0;
}
