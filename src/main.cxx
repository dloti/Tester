#include <iostream>
#include <sstream>
#include <string>
#include <fstream>
#include <typeinfo>
#include <cmath>
#include <map>
#include <vector>
#include <algorithm>
#include <stdlib.h>
#include "time.hxx"
#include "Instance.hxx"
#include "Expression.hxx"
#include "ConceptNode.hxx"
#include "RoleNode.hxx"
#include "BinaryOperator.hxx"
#include "Join.hxx"
#include "Not.hxx"
#include "InverseRole.hxx"
#include "TransitiveClosure.hxx"
#include "Equality.hxx"
#include "ValueRestriction.hxx"
#include "Rule.hxx"
#include "PreOps.hxx"
#include "ActionDenotations.hxx"

namespace mn {
using namespace std;
using namespace expression;

vector<Expression*> features;
map<string, int> policy;
vector<Expression*> rootConcepts;
vector<Expression*> rootRoles;
vector<string> primitiveConcepts;
vector<string> primitiveRoles;
vector<string> allObjects;
vector<int> allObjectsIdx;
vector<string> actions;
ActionDenotations* aDenot;
vector<Instance> instances;
vector<State> allStates;

PreOps* preops;
int denotationSize(0);
int runCount(1);

void get_all_states() {
	for (unsigned i = 0; i < instances.size(); ++i) {
		vector<State>* iStates = instances[i].GetStates();
		for (unsigned j = 0; j < iStates->size(); ++j) {
			allStates.push_back((*iStates)[j]);
		}
	}
}

void initialize_concepts() {
	for (unsigned i = 0; i < allObjects.size(); ++i)
		allObjectsIdx.push_back(i);
}

int get_obj_pos(string object) {
	int pos = std::find(allObjects.begin(), allObjects.end(), object)
			- allObjects.begin();
	if (pos >= allObjects.size()) {
		cout << "ERR " << object << endl;
		return -1;
	} else
		return pos;
}

void get_input() {
	string line;
	string field;
	ifstream fin("domain.txt");
	if (fin.is_open()) {
		int i = 0;
		while (!fin.eof() && getline(fin, line)) {
			istringstream iss(line);
			while (getline(iss, field, '\t')) {
				if (i == 0) {
					primitiveConcepts.push_back(field);
				} else if (i == 1) {
					primitiveRoles.push_back(field);
				} else if (i == 2) {
					allObjects.push_back(field);
				} else if (i == 3) {
					actions.push_back(field);
				}
			}
			i++;
		}
	}
	fin.close();
	fin.clear();
	fin.open("plans.txt");
	if (fin.is_open()) {
		while (!fin.eof() && getline(fin, line)) {
			Instance inst;
			istringstream iss(line);
			getline(iss, field, '\t');
			inst.SetNumPlan(atoi(field.c_str()));
			getline(iss, field, '\t');
			inst.SetNumActions(atoi(field.c_str()));

			for (int i = 0; i < inst.GetNumActions() + 1; ++i) {
				State s;
				vector<int> conceptInterpretation;
				vector<pair<int, int> > roleInterpretation;

				//for concepts
				for (unsigned j = 0; j < primitiveConcepts.size() - 1; ++j) {
					if (!fin.eof() && getline(fin, line)) {
						istringstream iss(line);
						getline(iss, field, '\t');
						string cname = field;
						getline(iss, field, '\t');
						istringstream interpretation(field);
						string object;
						while (getline(interpretation, object, ' ')) {
							int pos = get_obj_pos(object);
							if (pos > -1)
								conceptInterpretation.push_back(pos);
						}
						s.AddConceptInterpretation(cname,
								conceptInterpretation);
						conceptInterpretation.clear();
					}
				}
				//for roles
				for (unsigned j = 0; j < primitiveRoles.size(); ++j) {
					if ((!fin.eof() && getline(fin, line))) {
						istringstream iss(line);
						getline(iss, field, '\t');
						string rname = field;
						getline(iss, field, '\t');
						istringstream interpretation(field);
						string pair;
						while (getline(interpretation, pair, ' ')) {
							istringstream pairInterpretation(pair);
							string object;
							int pair_num = 0;
							std::pair<int, int> p;
							while (getline(pairInterpretation, object, ',')) {
								int pos = get_obj_pos(object);
								if (pos > -1) {
									if (pair_num == 0) {
										p.first = pos;
										++pair_num;
									} else {
										p.second = pos;
										pair_num = 0;
									}
								}
							}
							roleInterpretation.push_back(p);
						}
						//cout << endl;
						s.AddRoleInterpretation(rname, roleInterpretation);
						roleInterpretation.clear();
					}
				}

				if ((!fin.eof() && i < inst.GetNumActions()
						&& getline(fin, line))) {
					istringstream iss(line);
					getline(iss, field, ' ');
					s.SetAction(field);
					s.SetNumState(i);
					inst.AddState(s);
				} else if (i == inst.GetNumActions()) {
					inst.SetGoal(s);
				}
			}
			instances.push_back(inst);
		}
	}
	fin.close();
}

void printout() {
//Input print
//	cout << "Number of instances: " << instances.size() << endl;
//	for (unsigned i = 0; i < instances.size(); ++i) {
//		cout << instances[i].GetNumPlan() << " " << instances[i].GetNumActions() << endl;
//		for (unsigned j = 0; j < instances[i].GetStates().size(); ++j) {
//			instances[i].GetStates()[j].Print(allObjects);
//		}
//		instances[i].GetGoal().Print(allObjects);
//	}
//	cout << endl;
//	cout << "Primitive concepts" << endl;
//	for (unsigned i = 0; i < primitiveConcepts.size(); i++)
//		cout << primitiveConcepts[i] << "-";
//	cout << endl;
//	cout << "Primitive roles" << endl;
//	for (unsigned i = 0; i < primitiveRoles.size(); i++)
//		cout << primitiveRoles[i] << "-";
//	cout << endl;
//	for (unsigned i = 0; i < allObjects.size(); i++)
//		cout << allObjects[i] << "-";
//	cout << endl;
//	for (unsigned i = 0; i < actions.size(); i++)
//		cout << actions[i] << "-";
//	cout << endl;

//	for (unsigned i = 0; i < rootConcepts.size(); ++i) {
//		rootConcepts[i]->infix(cout);
//		cout << "-" << rootConcepts[i]->GetNonEmptyDenotationNum() << "-" << ((Operator*) rootConcepts[i])->GetLevel()
//				<< endl;
//		vector<vector<int> > denotations = rootConcepts[i]->GetDenotationVec();
//		for (unsigned j = 0; j < denotations.size(); ++j) {
//			for (unsigned k = 0; k < denotations[j].size(); ++k) {
//				cout << allObjects[denotations[j][k]] << " ";
//			}
//			cout << endl;
//		}
//	}
//
//	for (unsigned i = 0; i < rootRoles.size(); ++i) {
//		rootRoles[i]->infix(cout);
//		cout << endl;
//		vector<vector<pair<int, int> > > denotations = rootRoles[i]->GetDenotationRoleVec();
//		for (unsigned j = 0; j < denotations.size(); ++j) {
//			for (unsigned k = 0; k < denotations[j].size(); ++k) {
//				cout << "(" << allObjects[denotations[j][k].first] << "," << allObjects[denotations[j][k].second]
//						<< ") ";
//			}
//			cout << endl;
//		}
//	}

//	cout << "\tAction denotations" << endl;
//	for (unsigned i = 0; i < actions.size(); ++i) {
//		cout << actions[i] << ": ";
//		for (unsigned j = 0; j < (*aDenot)[i].size(); ++j) {
//			if ((*aDenot)[i][j])
//				cout << '+';
//			else
//				cout << '-';
//		}
//		cout << endl;
//	}

	cout << "Policy" << endl;
	map<string, int>::iterator it;
	for (it = policy.begin(); it != policy.end(); ++it)
		cout << it->first << " " << it->second << endl;
}

void cleanup() {
	for (unsigned i = 0; i < rootConcepts.size(); ++i) {
		delete rootConcepts[i];
	}

	for (unsigned i = 0; i < rootRoles.size(); ++i) {
		delete rootRoles[i];
	}

	rootConcepts.clear();
	rootRoles.clear();
}

Expression* find_expression(string line) {
	Expression* ex = NULL;
	stringstream ss;
	string cline;
	for (unsigned i = 0; i < rootConcepts.size(); ++i) {
		rootConcepts[i]->prefix(ss);
		getline(ss, cline);

		if (cline.compare(line) == 0) {
			//cout << cline << "-----" << line << endl;
			ex = rootConcepts[i];
			return ex;
		}
		ss.clear();
		cline.clear();
	}
	for (unsigned i = 0; i < rootRoles.size(); ++i) {
		rootRoles[i]->prefix(ss);
		getline(ss, cline);
		if (cline.compare(line) == 0) {
			//cout << cline << "-----" << line << endl;
			ex = rootRoles[i];
			return ex;
		}
		ss.clear();
		cline.clear();
	}
	return ex;
}

string get_inner(string str) {
	int parcnt = 0, chcnt = 0;
	bool validf(false), valids(false);
	for (unsigned i = 1; i < str.length(); ++i) {
		if (str[i] == '(') {
			parcnt++;
			validf = true;
			continue;
		}
		if (str[i] == ')') {
			parcnt--;
			if (parcnt == 0) {
				chcnt = i - 2;
				valids = true;
				break;
			}
		}
	}
	if (!validf || !valids) {
		cout << "ERR: " << str << " not valid" << endl;
		return "";
	}
	string ret(str, 2, chcnt);
	return ret;
}

vector<string> splitline(string line) {
	vector<string> ret;
	string str = get_inner(line), field;
	stringstream iss(str);
	int parcnt = 0, chcnt = 0;
	for (unsigned i = 1; i < str.length(); ++i) {
		if (str[i] == '(') {
			parcnt++;
			continue;
		}
		if (str[i] == ')')
			parcnt--;

		if (str[i] == ',' && parcnt == 0) {
			chcnt = i;
			break;
		}
	}
	string part(str, 0, chcnt);
	ret.push_back(part);
	part = str.substr(chcnt + 1, str.length() - 1);
	ret.push_back(part);
	return ret;
}

Expression* contruct_concept(string line) {
	Expression* ex = NULL;
	ex = find_expression(line);
	if (ex != NULL)
		return ex;

	if (line[0] == '!') {
		ex = new Not(contruct_concept(get_inner(line)), &allObjectsIdx, preops);
		ex->SetPreops(preops);
		ex->SimplifyDenotations();
		rootConcepts.push_back(ex);
	} else if (line[0] == '*') {
		ex = new TransitiveClosure(contruct_concept(get_inner(line)));
		ex->SetPreops(preops);
		ex->SimplifyDenotations();
		ex->SetRole(true);
		rootRoles.push_back(ex);
	} else if (line[0] == 'I') {
		ex = new InverseRole(contruct_concept(get_inner(line)));
		ex->SetPreops(preops);
		ex->SimplifyDenotations();
		ex->SetRole(true);
		rootRoles.push_back(ex);
//	} else if (line[0] == '^') {
//		vector<string> strv = splitline(line);
//		ex = new Join(contruct_concept(strv[0]), contruct_concept(strv[1]));
//		rootConcepts.push_back(ex);
	} else if (line[0] == '.') {
		vector<string> strv = splitline(line);
		ex = new ValueRestriction(contruct_concept(strv[0]),
				contruct_concept(strv[1]), preops);
		ex->SetPreops(preops);
		ex->SimplifyDenotations();
		rootConcepts.push_back(ex);
	} else if (line[0] == '=') {
		vector<string> strv = splitline(line);
		ex = new Equality(contruct_concept(strv[0]), contruct_concept(strv[1]),
				preops);
		ex->SetPreops(preops);
		ex->SimplifyDenotations();
		rootConcepts.push_back(ex);
	}
	return ex;
}

void read_policy() {
	string line;
	string field;
	vector<string> binDenots;
	ifstream fin("policy.txt");
	if (fin.is_open()) {
		int i = 0;
		Expression* ex;
		while (!fin.eof() && getline(fin, line)) {
			istringstream iss(line);
			if (i < 2) {
				while (getline(iss, field, ' ')) {
					if (i == 0) {
						ConceptNode* c = new ConceptNode(field);
						c->UpdateDenotations(instances, &allObjectsIdx);
						c->SetPreops(preops);
						c->SimplifyDenotations();
						rootConcepts.push_back(c);
						c = new ConceptNode(field);
						c->IsGoal(true);
						c->UpdateDenotations(instances, &allObjectsIdx);
						c->SetPreops(preops);
						c->SimplifyDenotations();
						rootConcepts.push_back(c);
					} else if (i == 1) {
						RoleNode* r = new RoleNode(field);
						r->UpdateDenotations(instances, &allObjectsIdx);
						r->SetPreops(preops);
						r->SimplifyDenotations();
						rootRoles.push_back(r);
						r = new RoleNode(field);
						r->IsGoal(true);
						r->UpdateDenotations(instances, &allObjectsIdx);
						r->SetPreops(preops);
						r->SimplifyDenotations();
						rootRoles.push_back(r);
					}
				}
			} else {
				if (i % 2 == 0) {
					ex = contruct_concept(line);
					features.push_back(ex);
				} else {
					binDenots.push_back(line);
				}
			}
			++i;
		}
	}
	fin.close();
	int act = -1;
	fin.open("actions.txt");
	int i = 0;
	string tmp;
	while (!fin.eof()) {
		fin >> act;
		//cout << act;

		for (int j = 0; j < binDenots.size(); ++j)
			tmp += binDenots[j][i];
		//cout << tmp << endl;
		policy[tmp] = act;
		tmp.clear();
		++i;
	}
	if (i != binDenots[0].size())
		cout << "ERR: wrong action file!" << i << ":"
				<< (binDenots[0].size() - 1) << endl;
	//cout << "I:" << i << "J:" << binDenots.size();
	//cout << endl;

//	for (i = 0; i < binDenots.size(); ++i) {
//		cout << binDenots[i] << endl;
//	}
}

int test() {
	int covered = 0;
	int correctly_covered = 0;
	cout << "TEST" << endl;
	for (unsigned j = 0; j < allStates.size(); ++j) {
		string tmp;
		for (unsigned i = 0; i < features.size(); ++i) {
			tmp += features[i]->GetSignature()[j];
		}
		if (policy.find(tmp) != policy.end()) {
			++covered;
			if (allStates[j].GetAction().compare(actions[policy[tmp]]) == 0)
				++correctly_covered;
		}
		else{
			//cout<<"Missed: "<<tmp<<endl;
		}
	}

	cout << "Correctly covered: " << correctly_covered << endl;
	return covered;
}

}
using namespace mn;

int main(int argc, char** argv) {
	get_input();
	initialize_concepts();
	preops = new PreOps(allObjects.size());
	aDenot = new ActionDenotations(&instances, &actions);
	read_policy();
	get_all_states();
	float t0, tf;
	t0 = time_used();
	printout();
	cout << "Covered: " << test() << " of " << allStates.size();
	tf = time_used();
	cout << endl << "Total time: ";
	report_interval(t0, tf, cout);
	cout << endl;
	cleanup();
	return 0;
}

