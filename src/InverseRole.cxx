/*
 * InverseRole.cxx
 *
 *  Created on: Mar 12, 2013
 *      Author: dloti
 */

#include "InverseRole.hxx"
namespace expression {
InverseRole::InverseRole(Expression *child) :
		UnaryOperator(child, 'I') {
	this->UpdateDenotations();
}

std::vector<std::pair<int, int> >* InverseRole::GetRoleInterpretation() {
	//this->UpdateInterpretation();
	return &(this->roleInterpretation);
}

void InverseRole::UpdateDenotations() {
	this->nonEmptyDenot = 0;
	this->denotationsRole.clear();
	std::vector<std::vector<std::pair<int, int> > > cDenot =
			this->child->GetDenotationRoleVec();
	for (unsigned i = 0; i < cDenot.size(); ++i) {
		std::vector<std::pair<int, int> > tmpInterpretation;
		for (unsigned j = 0; j < cDenot[i].size(); ++j) {
			std::pair<int, int> p(cDenot[i][j].second, cDenot[i][j].first);
				tmpInterpretation.push_back(p);
		}
		if (tmpInterpretation.size() > 0)
			this->nonEmptyDenot++;
		this->denotationsRole.push_back(tmpInterpretation);
	}
}

void InverseRole::UpdateInterpretation() {
	//TODO Correct find
	this->child->UpdateInterpretation();
	ClearInterpretation();
	std::vector<std::pair<int, int> >* childInterpretation =
			(this->child)->GetRoleInterpretation();

	if (childInterpretation == NULL || childInterpretation->size() == 0)
		return;

	std::vector<std::pair<int, int> >::iterator first =
			childInterpretation->begin(), last = childInterpretation->end();

	for (; first != last; ++first) {
		std::pair<int, int>* p = new std::pair<int, int>(first->second,
				first->first);
		if (std::find(childInterpretation->begin(), last, *p) != last)
			this->roleInterpretation.push_back(*p);
		else
			delete p;
	}
}

InverseRole::~InverseRole() {
	// TODO Auto-generated destructor stub
}
}

