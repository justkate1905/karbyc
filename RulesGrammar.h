#ifndef RULESGRAMMAR_H
#define RULESGRAMMAR_H

#include <iostream>
#include <string>
#include <fstream>
#include <map>
#include <boost/spirit/include/qi.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/bind.hpp>
#include <boost/spirit/include/phoenix.hpp>
#include <boost/fusion/include/adapt_struct.hpp>

namespace Logic
{
	namespace qi = boost::spirit::qi;
	namespace ascii = boost::spirit::ascii;
	using namespace std;
	using namespace qi;
	using namespace boost::spirit;
	namespace phx = boost::phoenix;
	typedef int size_opcode;
	typedef std::wstring str_t;
	typedef str_t::iterator str_t_it;

	//��������� �������� ���������� � �����������
	//addr - ����� ���������� � ����������� �����
	//name - ��� ���������� � �������� ����
	struct variables{
		int addr = 0;
		int buff_addr;
		int type=0;
		int var_num = 1;
		str_t name;
		str_t name_buff;
	};
	
	//��������� ������������� ��������� �������������� ��������
	//first - ������ �������
	//second - ������ �������
	struct operand{
		int first;
		int second;
	};
	
	
	//��������� ������������� ������� �������������� ��������
	struct signs{
		int PLUS = 0x1003;
		int MINUS = 0x1007;
		int MULTI = 0x100B;
		int DIV = 0x100F;
	};


	template <typename Iterator>
	class RulesGrammar : public qi::grammar <Iterator,  qi::space_type >
	{
		//����������
		variables v;
		//���.��������
		signs s;
		//��������
		operand op_term, op_factor;
		//���������� ��� �������� �������� ����������, ���� ������ � ����� ����������-�����
		int num=0, type = 0x00AB, var_flag=0, buff_flag=0, count_op = 0;
		
		std::string var_name = " ", math_exp, str_value, sign, name1;
		//������ ����� ��������
		vector <size_opcode> opcodes;
		vector<int> stack, var_stack; 
		//������� ���� ����������
		map<str_t, int> var_v;
		//������ ������� ��������������� ��������� � �������� �������� ������		
		vector<int> math_reverse_form;
		//���������� ������
		qi::rule<Iterator, qi::space_type> start_programm, programm, name, variable, associate, binding, uint_bind, double_bind,char_bind,expression, term,factor,cond, start_prog, condition, operations, stream, init,id;

	public:
		RulesGrammar() : RulesGrammar::base_type(start_programm)
		{
				//������ ���������
				start_programm = qi::lit("start")[boost::bind(&RulesGrammar::PushOpcode, this, 0x00A1)] 
								>>'('>>qi::char_(')')>>qi::char_('{')>>programm>>'}';
				//��������� ���������� � ���������� ����������, ���� ����, ���� ���				
				programm = -(qi::lit("var")>>variable>>*(','>>variable) >> ';')>>start_prog;
				//���������� ���������� + ��������� �������������
				variable = (name[boost::bind(&RulesGrammar::PushOpcode, this, 0x00AB)]
								[boost::bind(&RulesGrammar::PushVar, this)]
								[boost::bind(&RulesGrammar::PushOpcode, this, 1)]
								[boost::bind(&RulesGrammar::PushOpcode, this, 0)]
								>> -(init))
								[boost::bind(&RulesGrammar::PushVarNum, this)];
				//�������� ������������
				associate = (qi::char_('=') >> (expression
												[boost::bind(&RulesGrammar::Resolve, this)]
												[boost::bind(&RulesGrammar::PushOpcode, this, 0x3001)]
												[boost::bind(&RulesGrammar::PushBuffAddr, this)]
												[boost::bind(&RulesGrammar::PushOpcode, this, 0x00AA)] | 
												name 
												[boost::bind(&RulesGrammar::PushOpcode, this, 0x3000)]
												[boost::bind(&RulesGrammar::PushBuffAddr, this)]
												[boost::bind(&RulesGrammar::SetBuffName, this)]
												[boost::bind(&RulesGrammar::PushBuffAddr, this)]
												));
				//�������������
				init = qi::char_('=') >> binding;
				//����������� ���������������� ��������
				binding = ( uint_bind|double_bind |'"'
							>>char_bind>> *(qi::char_("0-9a-zA-Z")
											[phx::bind(&RulesGrammar::PushOpcode, this, qi::_1)]
											[boost::bind(&RulesGrammar::Increase, this)]) >>'"');
				//����������� �����
				uint_bind = int_[boost::bind(&RulesGrammar::TakeStack, this, 0x00AB)]
							[boost::bind(&RulesGrammar::PushOpcode, this, this->v.var_num)]
							[phx::bind(&RulesGrammar::PushOpcode, this, qi::_1)];
				//������� 
				double_bind = double_[boost::bind(&RulesGrammar::TakeStack, this, 0x00AB)]
							[boost::bind(&RulesGrammar::PushOpcode, this, this->v.var_num)]
							[phx::bind(&RulesGrammar::PushOpcode, this, qi::_1)];
				//����������
				char_bind = qi::char_[boost::bind(&RulesGrammar::TakeStack, this, 0x00AC)]
							[boost::bind(&RulesGrammar::PushOpcode, this, 1)]
							[phx::bind(&RulesGrammar::PushOpcode, this, qi::_1)]; 
				//��� ����������
				name = qi::as_wstring[+(qi::alpha|'_')>> *(qi::alnum|'_')]
						[phx::bind(&RulesGrammar::SetName, this, qi::_1)]; 
				
				//���� ��������� ������
				//�������, �������������� ��������, �������� ������
				start_prog = *((condition | stream|operations));
				//�������� ������
				stream = qi::lit("out")
						>> (name[boost::bind(&RulesGrammar::PushOpcode, this, 0x00C8)]
								[boost::bind(&RulesGrammar::SetBuffName, this)] 
								[boost::bind(&RulesGrammar::PushBuffAddr, this)]
							| uint_bind[boost::bind(&RulesGrammar::PushOpcode, this, 0x00C9)]
										[boost::bind(&RulesGrammar::PushValue, this)] 
							| double_bind[boost::bind(&RulesGrammar::PushOpcode, this, 0x00C9)]
										[boost::bind(&RulesGrammar::PushValue, this)]  
							| (qi::lit('"')[boost::bind(&RulesGrammar::PushOpcode, this, 0x00CA)]
							>> *(qi::char_[phx::bind(&RulesGrammar::SetNum, this, qi::_1)]
											[boost::bind(&RulesGrammar::PushValue, this)])>>'"') )
						  >> ';';
				//�������������� ��������
				operations = name [boost::bind(&RulesGrammar::SetBuffName, this)] >> associate 							
							// | formules | ("\" " >> *(alpha|alnum|blank|lower|upper|"_"|)));
							>>';';
				//�������
				condition = qi::lit("if")>>'('>>cond>>')'>>qi::char_('{')>>start_prog >> '}';
				//�������� ���������
				cond = name >> ((('>'|qi::lit(">=")|'<'|qi::lit("<="))>>(int_|double_))|"==">>(int_|double_|('"'>>*(qi::char_)>>'"'))); 
				//������� �������������� ���������
				expression = term [boost::bind(&RulesGrammar::CheckSetTerm, this,1)]  >> 
							*((qi::char_('-') >> term[boost::bind(&RulesGrammar::CheckSetTerm, this,2)])
									[boost::bind(&RulesGrammar::SetSign, this, 1,2)]
									[boost::bind(&RulesGrammar::SetFlag, this,0)]  
									[boost::bind(&RulesGrammar::CheckSetTerm, this,1)]
									[boost::bind(&RulesGrammar::CheckAndSetOpcodeTerm, this)]
							| (qi::char_('+') >> term [boost::bind(&RulesGrammar::CheckSetTerm, this, 2)]) 
									[boost::bind(&RulesGrammar::SetSign, this, 0,2)]
									[boost::bind(&RulesGrammar::SetFlag, this,0)]
									[boost::bind(&RulesGrammar::CheckSetTerm, this,1)]
									[boost::bind(&RulesGrammar::CheckAndSetOpcodeTerm, this)]);
                //��������� ��������� � �������
				term       =  factor[boost::bind(&RulesGrammar::CheckSetFactor, this,1)]
									>> 
							*( ('*' >> factor[boost::bind(&RulesGrammar::CheckSetFactor, this,2)])
										[boost::bind(&RulesGrammar::SetSign, this, 2,1)] 
										[boost::bind(&RulesGrammar::SetFlag, this,0)]

							| ('/' >> factor[boost::bind(&RulesGrammar::CheckSetFactor, this,2)] )
										[boost::bind(&RulesGrammar::SetSign, this, 3,1)]
										[boost::bind(&RulesGrammar::SetFlag, this,0)]);
										
				factor     = (name[boost::bind(&RulesGrammar::PushName, this)]
									[boost::bind(&RulesGrammar::SetBuffFlag, this, 1)]
							| qi::uint_[phx::bind(&RulesGrammar::SetMath, this, qi::_1)]
                           |  '(' >> expression >> ')' );
		}
		//��������� ��������� ��������
		void SetNum(int i){
			num =i;
		}
		void SetVarStack(int i){
			var_stack.push_back(i);
		}
		
		void Increase(){
			v.var_num++;
		}
		void PushVarNum(){
			int i = opcodes.size();
			opcodes.at(i-v.var_num-1) = v.var_num;
			v.var_num = 1;
		}
		
		void TakeStack(int fl){
			opcodes.pop_back();
			opcodes.pop_back();
			opcodes.pop_back();
			PushOpcode(fl);
		}
		
		void ClearStack(){
			var_stack.clear();
		}
		void PushStr(){
			
		}
		void FinalPushStr(){
			
			
		}
		//��������� ����
//		void SetType(int i){
//			v.type =i;
//		}
		//��������� ����� ����������
		void SetName(str_t name){
			v.name = name;
		}
		//��������� ����� ����������-�����
		void SetFlag(int val){
			var_flag = val;
		}
		void SetBuffFlag(int val){
			buff_flag = val;
		}
		//��������� ������ ����������
		void SetAddr(int address){
			v.addr = address;
		}
		
		void SetBuffName(){
			v.name_buff = v.name;
			v.buff_addr = FindVarVal(v.name_buff);
		}
		void PushBuffAddr(){
			opcodes.push_back(v.buff_addr);
		}
		
		void SetOp(vector<int> opcode){
			opcodes = opcode;
		}
		//������ � ������ �������� �������� ������ ��������� ��������
		void SetMath(int val){
			SetFlag(0);
			math_reverse_form.push_back(val);
			cout<<"=========================="<<endl;
			cout<<math_reverse_form.back()<<endl;
		}
		//��������� ������� �������������� ��������
		void SetSignStruct(int plus, int minus, int multi, int div){
			s.PLUS = plus;
			s.MINUS = minus;
			s.MULTI = multi;
			s.DIV = div;
		}
		//������ � ������ ��� ������� ���.��������
		void SetSign(int op_sign, int f){
			switch(f){
				case 1:
					CheckAndSetOpcodeFactor();
					break;
				case 2:
					CheckAndSetOpcodeTerm();
					break;
			}
			switch(op_sign){
				case 0:
					math_reverse_form.push_back(s.PLUS);
					break;
				case 1:
					math_reverse_form.push_back(s.MINUS);
					break;
				case 2:
					math_reverse_form.push_back(s.MULTI);
					break;
				case 3:
					math_reverse_form.push_back(s.DIV);
					break;
			}
			cout<<"=========================="<<endl;
			cout<<math_reverse_form.back()<<endl;
		}
		
		//������ � ������� ����������
		map<str_t, int> GetVar(){
			return var_v;
		}
		//������ � ������� �������
		vector <size_opcode> GetOp(){
			return opcodes;
		}
		//������ � ������� ���
		vector<int> GetMath(){
			return math_reverse_form;
		}
		//�������� ������ �������� � ����������� ���� (���������� ��� �����) �� �����
		void CheckSetTerm(int num){
			cout<<"~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"<<endl;
			cout<< var_flag<<endl;
			switch(num){
				case 1:
					op_term.first = var_flag;
					break;
				case 2:
					op_term.second = var_flag;
					break;
			}
			//var_flag = 0;
		}
		void CheckSetFactor(int num){
			cout<<"######################"<<endl;
			cout<< var_flag<<endl;
			switch(num){
				case 1:
					op_factor.first = var_flag;
					break;
				case 2:
					op_factor.second = var_flag;
					break;
			}
			//var_flag = 0;
		}
		//��������� ������� ���.�������� � ����������� �� ���������
		void CheckAndSetOpcodeTerm(){
			if(op_term.first==0){
				if(op_term.second==0){
					SetSignStruct(0x1003,0x1007,0x100B,0x100F);
				}
				else{
					SetSignStruct(0x1002,0x1006,0x100A,0x100E);
				}
			}
			else{
				if(op_term.second==0){
					SetSignStruct(0x1001,0x1005,0x1009,0x100D);
				}
				else{
					SetSignStruct(0x1000,0x1004,0x1008,0x100C);
				}				
			}
		}
		void CheckAndSetOpcodeFactor(){
			if(op_factor.first==0){
				if(op_factor.second==0){
					SetSignStruct(0x1003,0x1007,0x100B,0x100F);
				}
				else{
					SetSignStruct(0x1002,0x1006,0x100A,0x100E);
				}
			}
			else{
				if(op_factor.second==0){
					SetSignStruct(0x1001,0x1005,0x1009,0x100D);
				}
				else{
					SetSignStruct(0x1000,0x1004,0x1008,0x100C);
				}				
			}
		}
		
		
		//��������� ������ ����������
		int FindVarVal(str_t val){
			auto map<str_t,int>::iterator it = var_v.find(val);
			if(it != var_v.end()){
				return (it->second);
				}
			else{
				return -1;
			}
		}
		//������ ������ ���������� � ������ �������
		void PushAddr(std::string val){
			opcodes.push_back(FindVarVal(val));
		}
		//������ ������ � ������
		void PushOpcode(int opcode){
			opcodes.push_back(opcode);			
		}
		//
		void PushOperation(){
			while(math_reverse_form.size()!=0){
				opcodes.push_back(math_reverse_form.back());	
				math_reverse_form.pop_back();	
			}
		}
		//��������� ����� ����������-����� � ������ ������ � ������ � ���
		void PushName(){
			SetFlag(1);
			//int index = FindVarVal(v.name)/sizeof(size_opcode) - 3;
			math_reverse_form.push_back(FindVarVal(v.name));	
			cout<<"=========================="<<endl;
			cout<<math_reverse_form.back()<<endl;
		}

		//������ � ������ ������� �����
		void PushValue(){
			opcodes.push_back(num);
			num = 0;
		}	
		//���������� � ������� ������ ���� ���_����������, �����
		void PushVar()
		{
			int addr = (4 + opcodes.size()-1)*sizeof(size_opcode);
			SetAddr(addr);
			var_v.insert(pair<str_t,int>(v.name, v.addr));
		}
		void Resolve(){
			int a,i=0;
			vector<int>::iterator it = math_reverse_form.begin();
			while(it!=math_reverse_form.end()){
				cout<<std::hex<<(*it)<< " ";
				if(CheckOperation((*it))){
					stack.push_back((*it));
					it++;
				}
				else{
					//if(i==0){
						PushOpcode((*it));
						a = stack.back();
						stack.pop_back();
						if(stack.back()==0x00AA && a==0x00AA){
							PushOpcode(0x00A9);
						}
						else{
							PushOpcode(stack.back());
						}
						PushOpcode(a);
						stack.pop_back();
						stack.push_back(0x00AA);
						it++;
						i++;
					//}
					/*else{
						PushOpcode((*it));
						PushOpcode(0x89AB);
						PushOpcode(stack.back());
						stack.pop_back();
						it++;
					}*/
					
				}
			}
			cout<<"~~~~~~~ "<<FindVarVal(v.name_buff)<<" ~~~~~~~~"<<endl;
			math_reverse_form.clear();
		}
		bool CheckOperation(int val){
			if(val!=0x1000 && val!=0x1001 && val!=0x1002 && val!=0x1003 && val!=0x1004 && val!=0x1005&&val!=0x1006&&val!=0x1007&&val!=0x1008&&val!=0x1009&&val!=0x100A&&val!=0x100B&&val!=0x100C&&val!=0x100D&&val!=0x100E&&val!=0x100F){
				return true;
			}
			else{
				return false;
			}
		}
		
	};
}
#endif 