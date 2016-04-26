#include "RulesGrammar.h"
//using namespace std;
//using namespace boost::spirit;
using namespace Logic;

const int i = 1;
#define is_bigendian() ( (*(char*)&i) == 0 )
	//функция по определению порядка записи байтов для корректной записи кодов операций в бинарный файл
int reverseInt(int s) {
	char c1, c2, c3, c4;
	int c5;
	if (is_bigendian()) {
		return s;
	} else {
		c1 = s & 0xFF;
		c2 = (s & 0xFF00) >> 8;
		c3 = (s & 0xFF0000) >> 16;
		c4 = (s & 0xFF000000)>> 24;
		c5 = (c1 << 24) ^ (c2<<16) ^ (c3<<8) ^ c4;
		return c5;
	}
}
	//namespace qi = boost::spirit::qi;
	//using namespace qi;
int main(int argc, char* argv[])
{
		setlocale(0,"");
		FILE *file;
		char* name = "file.txt";
		char* binary; 
		RulesGrammar<str_t_it> rulesGrammar;
		if(argc==1){
			cout<<"There's no filename"<<endl;
			}
		else{
			name = argv[1];
			if(argc == 3){
				binary = argv[2];
			}
			else{
				binary = "binary.bin";
			}
		}
		ifstream f(name);
		if(!f.is_open()){
			cout<< "This file is not exist!"<<endl;
			f.close();
			}
		else{
			str_t S,str;
			while(!f.eof()){
				getline(f,S);
				if(S.find_first_not_of("\t")!=0){
					//S=S.substr(S.find_first_not_of("\t"));
				}
				str+= S;
				str+=(wchar_t)(' ');
			}
			cout<<str<<endl;
			vector<size_opcode> opcode(4);
			vector<variables> var_v;
		
			str_t_it begin = str.begin(), end = str.end();
			bool success = Logic::qi::phrase_parse(begin, end, rulesGrammar, Logic::qi::space);
			cout << "---------------------\n";
					if(success && begin == end)
							std::cout << "Parsing succeeded\n";
					else
							std::cout << "Parsing failed\nstopped at: " <<"\""
									  << str_t(begin, end) << "\"\n";
			
			for(int i =0; i<rulesGrammar.GetOp().size(); i++){
				opcode.push_back(rulesGrammar.GetOp().at(i));
				} 
				
			vector<size_opcode>::const_iterator it = find(opcode.begin(), opcode.end(), 0x00A1);
			opcode.at(1) = (it - opcode.begin())*sizeof(opcode.at(0));	
			opcode.at(0) = sizeof(opcode.at(0))*opcode.size();
			opcode.at(3) = sizeof(opcode.at(0))*(opcode.size()-(it - opcode.begin()));
			
				
			cout<<"==================="<<endl;
			/*for(int i=0; i<rulesGrammar.GetVar().size(); i++ ){
			cout << rulesGrammar.GetVar().at(i).addr << " "<< rulesGrammar.GetVar().at(i).name<<endl;
			}*/
			opcode.at(2) = rulesGrammar.GetVar().size();
			file=fopen(binary,"wb+");
			for(int i =0; i<opcode.size(); i++){
				cout<<std::hex<<opcode.at(i)<<endl;
				//opcode.at(i) = reverseInt(opcode.at(i));
				fwrite(&opcode.at(i), sizeof(opcode.at(i)), 1, file);
			}
			/*for(int i =0; i< opcode.size(); i++){
				cout<<std::hex<<opcode.at(i)<<endl;
			}*/
			
			for(int i =0; i<rulesGrammar.GetMath().size(); i++){
					cout<<rulesGrammar.GetMath().at(i)<<" ";
			}
		}
		//cout<<rulesGrammar.GetMath().at(2)<<endl;
		system("pause");
		
		return 0;
}