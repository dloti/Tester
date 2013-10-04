/*
 * Operand.hxx
 *
 *  Created on: Feb 26, 2013
 *      Author: dloti
 */

#ifndef OPERAND_HXX_
#define OPERAND_HXX_
#include "Expression.hxx"
namespace expression {
class Operand: public Expression {
protected:
	bool goal;
	std::string predicate;
public:
	Operand();
	virtual void UpdateDenotations(std::vector<Instance> instances,
			std::vector<int>* allObjects) = 0;
	void print(std::ostream& s) const {
		s << predicate;
		if (goal)
			s << "g";
	}
	void infix(std::ostream& s) const {
		print(s);
	}

	void prefix(std::ostream& s) const {
		print(s);
	}
	inline std::string GetPredicate() {
		return predicate;
	}

	bool IsGoal();
	void IsGoal(bool goal);

	virtual ~Operand();
	inline std::vector<Expression*> GetChildren() {
		std::vector<Expression*> ret;
		ret.push_back(this);
		return ret;
	}
};
}

#endif /* OPERAND_HXX_ */
