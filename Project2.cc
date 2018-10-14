/*
 * Copyright (C) Mohsen Zohrevandi, 2017
 *
 * Do not share this file with anyone
 */
#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>

#include "lexer.h"

using namespace std;

Token t;
LexicalAnalyzer lexer;

vector<string> nonTerminals;
vector<string> terminals;

vector<string> orderedNonTerminals;
vector<string> orderedTerminals;

vector<string> universalOrderedNonTerminals;
vector<string> universalOrderedTerminals;

int firstSet[100][100];
vector<string> tempFIRSTOutput;

int followSet[100][100];

struct Rule
{
    string LHS;
    vector<string> RHS;
};

vector<Rule> ruleList;

void syntax_error()
{
    cout << "SYNTAX ERROR\n";
    exit(1);
}

Token expect(TokenType expected_type)
{
    Token t = lexer.GetToken();
    if (t.token_type != expected_type)
        syntax_error();
    return t;
}

void copyIntegerArray(int arr1[],int arr2[],int len)
{
    for(int i = 0; i < len; i++)
    {
        arr2[i] = arr1[i];
    }
}

int index_Of(string arr[],int len, string item)
{
    for(int i = 0; i < len; i++)
    {
        if(arr[i] == item)
        {
            return i;
        }
    }
    return -1;
}

bool intArrayAreEqual(int arr1[], int arr2[], int len)
{
    for( int i = 0; i <len ; i++)
    {
        if(arr1[i] != arr2[i])
        {
            return false;
        }
    }
    return true;
}

bool inTerminalList(string item)
{
    if(terminals.size()==0)
    {
        return false;
    }
    else
    {
        for (auto i : terminals)
        {
            if(i == item)
            {
                return true;
            }
        }
    }
    return false;
}

bool inNonTerminalList(string item)
{
    if(nonTerminals.size()==0)
    {
        return false;
    }
    else
    {
        for (auto i : nonTerminals)
        {
            if(i == item)
            {
                return true;
            }
        }
    }
    return false;
}

void addFIRST(int arr1[], int arr2[],int len)
{
    for(int i = 0; i < len; i++)
    {
        if(arr1[i] == 1 && universalOrderedTerminals[i] != "#")
        {
            arr2[i] = 1;
        }
    }
}

void calculateFIRST()
{
    if(!(find(begin(universalOrderedTerminals), end(universalOrderedTerminals), "#") != end(universalOrderedTerminals)))
    {
        universalOrderedTerminals.push_back("#");
        int FIRST[100][100];

        for(int i = 0; i < universalOrderedNonTerminals.size(); i++)
        {
            for(int j = 0; j < universalOrderedTerminals.size(); j++)
            {
                FIRST[i][j] = 0;
            }
        }

        string nonTerm[universalOrderedNonTerminals.size()];
        string term[universalOrderedTerminals.size()];
        for(int i = 0; i < universalOrderedNonTerminals.size();i++)
        {
            nonTerm[i] = universalOrderedNonTerminals[i];
        }
        for(int i = 0; i < universalOrderedTerminals.size();i++)
        {
            term[i] = universalOrderedTerminals[i];
        }

        int tempFIRST[100][100];

        //Copy FIRST to TempFIRST
        for(int i = 0; i < universalOrderedNonTerminals.size() ; i++)
        {
            for(int j = 0; j < universalOrderedTerminals.size() ; j++)
            {
                tempFIRST[i][j] = FIRST[i][j];
            }
        }

        bool firstAreEqual;
        do
        {
            firstAreEqual = true;
            //Copy tempFIRST to FIRST
            for(int i = 0; i < universalOrderedNonTerminals.size() ; i++)
            {
                for(int j = 0; j < universalOrderedTerminals.size() ; j++)
                {
                    FIRST[i][j] = tempFIRST[i][j];
                }
            }
            //Applying rule 3 of FIRST SET to all the rules in the grammar
            for(auto rule : ruleList)
            {
                if(inNonTerminalList(rule.RHS[0]))
                {
                    addFIRST(tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[0])],tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.LHS)],universalOrderedTerminals.size());
                }
                else if(inTerminalList(rule.RHS[0]))
                {
                    tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.LHS)][index_Of(term,universalOrderedTerminals.size(),rule.RHS[0])] = 1;
                }
            }

            //Applying Rule 4 of FIRST SET to all the rules
            for(auto rule : ruleList)
            {
                if(rule.RHS.size() > 1)
                {
                    if(inNonTerminalList(rule.RHS[0]) && tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[0])][index_Of(term,universalOrderedTerminals.size(),"#")] == 1)
                    {
                        if(inNonTerminalList(rule.RHS[1]))
                        {
                            addFIRST(tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[1])],tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.LHS)],universalOrderedTerminals.size());
                            for(int i = 1 ; i < rule.RHS.size() - 1; i++)
                            {
                                if(inNonTerminalList(rule.RHS[i]) && tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[i])][index_Of(term,universalOrderedTerminals.size(),"#")] == 1)
                                {
                                    if(inNonTerminalList(rule.RHS[i+1]))
                                    {
                                        addFIRST(tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[i+1])],tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.LHS)],universalOrderedTerminals.size());
                                    }
                                    else if(inTerminalList(rule.RHS[i+1]))
                                    {
                                        tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.LHS)][index_Of(term,universalOrderedTerminals.size(),rule.RHS[i+1])] = 1;
                                        break;
                                    }
                                }
                            }
                        }
                        else if(inTerminalList(rule.RHS[1]))
                        {
                            tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.LHS)][index_Of(term,universalOrderedTerminals.size(),rule.RHS[1])] = 1;
                        }
                    }
                }
                else
                {
                    continue;
                }
            }

            //Applying rule 5 of FIRST SET to all the rules
            for(auto rule : ruleList)
            {
                bool canBeEpsilon = true;
                for(auto item : rule.RHS)
                {
                    if(!inNonTerminalList(item))
                    {
                        canBeEpsilon = false;
                        break;
                    }
                    else
                    {
                        if(tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),item)][index_Of(term,universalOrderedTerminals.size(),"#")] != 1)
                        {
                            canBeEpsilon = false;
                            break;
                            }
                    }
                }
                if(canBeEpsilon)
                {
                    tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.LHS)][index_Of(term,universalOrderedTerminals.size(),"#")] = 1;
                }
            }

            for(int i = 0; i < universalOrderedNonTerminals.size() ; i++)
            {
                for(int j = 0; j < universalOrderedTerminals.size() ; j++)
                {
                    if(tempFIRST[i][j] != FIRST[i][j])
                    {
                        firstAreEqual = false;
                    }
                }
            }
        }while(!firstAreEqual);

        //Copy FIRST to global FIRST set
        for(int i = 0; i < universalOrderedNonTerminals.size(); i++)
        {
            for(int j = 0; j < universalOrderedTerminals.size(); j++)
            {
                firstSet[i][j] = FIRST[i][j];
            }
        }

        for(int i = 0; i < universalOrderedNonTerminals.size(); i++)
        {
            int epsilonIndex = -1;

            tempFIRSTOutput.push_back("F");
            tempFIRSTOutput.push_back("I");
            tempFIRSTOutput.push_back("R");
            tempFIRSTOutput.push_back("S");
            tempFIRSTOutput.push_back("T");
            tempFIRSTOutput.push_back("(");
            tempFIRSTOutput.push_back(nonTerm[i]);
            tempFIRSTOutput.push_back(")");
            tempFIRSTOutput.push_back(" ");
            tempFIRSTOutput.push_back("=");
            tempFIRSTOutput.push_back(" ");
            tempFIRSTOutput.push_back("{");
            tempFIRSTOutput.push_back(" ");

            //Get the position of epsilon in FIRST set
            for(int j = 0; j < universalOrderedTerminals.size(); j++)
            {
                if(firstSet[i][j] == 1 && term[j] == "#")
                {
                    epsilonIndex = j;
                    break;
                }
            }

            if(epsilonIndex == -1)
            {
                for(int j = 0; j < universalOrderedTerminals.size(); j++)
                {
                    if(firstSet[i][j] == 1)
                    {
                        tempFIRSTOutput.push_back(term[j]);
                        tempFIRSTOutput.push_back(",");
                        tempFIRSTOutput.push_back(" ");
                    }
                }
                tempFIRSTOutput.push_back("}");
                tempFIRSTOutput.push_back("\n");
            }
            else
            {
                tempFIRSTOutput.push_back("#");
                tempFIRSTOutput.push_back(",");
                tempFIRSTOutput.push_back(" ");
                for(int j = 0; j < universalOrderedTerminals.size(); j++)
                {
                    if(firstSet[i][j] == 1)
                    {
                        if(j != epsilonIndex)
                        {
                            tempFIRSTOutput.push_back(term[j]);
                            tempFIRSTOutput.push_back(",");
                            tempFIRSTOutput.push_back(" ");
                        }
                        else
                        {
                            continue;
                        }
                    }
                }
                tempFIRSTOutput.push_back("}");
                tempFIRSTOutput.push_back("\n");
            }
        }
    }
    else
    {
        if((find(begin(universalOrderedTerminals), end(universalOrderedTerminals), "#") != end(universalOrderedTerminals)))
        {
            int FIRST[100][100];

            for(int i = 0; i < universalOrderedNonTerminals.size(); i++)
            {
                for(int j = 0; j < universalOrderedTerminals.size(); j++)
                {
                    FIRST[i][j] = 0;
                }
            }

            string nonTerm[universalOrderedNonTerminals.size()];
            string term[universalOrderedTerminals.size()];
            for(int i = 0; i < universalOrderedNonTerminals.size();i++)
            {
                nonTerm[i] = universalOrderedNonTerminals[i];
            }
            for(int i = 0; i < universalOrderedTerminals.size();i++)
            {
                term[i] = universalOrderedTerminals[i];
            }

            int tempFIRST[100][100];

            //Copy FIRST to TempFIRST
            for(int i = 0; i < universalOrderedNonTerminals.size() ; i++)
            {
                for(int j = 0; j < universalOrderedTerminals.size() ; j++)
                {
                    tempFIRST[i][j] = FIRST[i][j];
                }
            }

            bool firstAreEqual;
            do
            {
                firstAreEqual = true;
                //Copy tempFIRST to FIRST
                for(int i = 0; i < universalOrderedNonTerminals.size() ; i++)
                {
                    for(int j = 0; j < universalOrderedTerminals.size() ; j++)
                    {
                        FIRST[i][j] = tempFIRST[i][j];
                    }
                }

                //Applying rule 3 of FIRST SET to all the rules in the grammar
                for(auto rule : ruleList)
                {
                    if(inNonTerminalList(rule.RHS[0]))
                    {
                        addFIRST(tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[0])],tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.LHS)],universalOrderedTerminals.size());
                    }
                    else if(inTerminalList(rule.RHS[0]))
                    {
                        tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.LHS)][index_Of(term,universalOrderedTerminals.size(),rule.RHS[0])] = 1;
                    }
                }

                //Applying Rule 4 of FIRST SET to all the rules
                for(auto rule : ruleList)
                {
                    if(rule.RHS.size() > 1)
                    {
                        if(inNonTerminalList(rule.RHS[0]) && tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[0])][index_Of(term,universalOrderedTerminals.size(),"#")] == 1)
                        {
                            if(inNonTerminalList(rule.RHS[1]))
                            {
                                addFIRST(tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[1])],tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.LHS)],universalOrderedTerminals.size());
                                for(int i = 1 ; i < rule.RHS.size() - 1; i++)
                                {
                                    if(inNonTerminalList(rule.RHS[i]) && tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[i])][index_Of(term,universalOrderedTerminals.size(),"#")] == 1)
                                    {
                                        if(inNonTerminalList(rule.RHS[i+1]))
                                        {
                                            addFIRST(tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[i+1])],tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.LHS)],universalOrderedTerminals.size());
                                        }
                                        else if(inTerminalList(rule.RHS[i+1]))
                                        {
                                            tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.LHS)][index_Of(term,universalOrderedTerminals.size(),rule.RHS[i+1])] = 1;
                                            break;
                                        }
                                    }
                                    else
                                    {
                                        break;
                                    }
                                }
                            }
                            else if(inTerminalList(rule.RHS[1]))
                            {
                                tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.LHS)][index_Of(term,universalOrderedTerminals.size(),rule.RHS[1])] = 1;
                            }
                        }
                    }
                    else
                    {
                        continue;
                    }
                }

                //Applying rule 5 of FIRST SET to all the rules
                for(auto rule : ruleList)
                {
                    bool canBeEpsilon = true;
                    for(auto item : rule.RHS)
                    {
                        if(!inNonTerminalList(item))
                        {
                            canBeEpsilon = false;
                            break;
                        }
                        else
                        {
                            if(tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),item)][index_Of(term,universalOrderedTerminals.size(),"#")] != 1)
                            {
                                canBeEpsilon = false;
                                break;
                            }
                        }
                    }
                    if(canBeEpsilon)
                    {
                        tempFIRST[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.LHS)][index_Of(term,universalOrderedTerminals.size(),"#")] = 1;
                    }
                }

                for(int i = 0; i < universalOrderedNonTerminals.size() ; i++)
                {
                    for(int j = 0; j < universalOrderedTerminals.size() ; j++)
                    {
                        if(tempFIRST[i][j] != FIRST[i][j])
                        {
                            firstAreEqual = false;
                        }
                    }
                }
            }while(!firstAreEqual);

            //Copy FIRST to global FIRST Set
            for(int i = 0; i < universalOrderedNonTerminals.size(); i++)
            {
                for(int j = 0; j < universalOrderedTerminals.size(); j++)
                {
                    firstSet[i][j] = FIRST[i][j];
                }
            }

            for(int i = 0; i < universalOrderedNonTerminals.size(); i++)
            {
                int epsilonIndex = -1;

                tempFIRSTOutput.push_back("F");
                tempFIRSTOutput.push_back("I");
                tempFIRSTOutput.push_back("R");
                tempFIRSTOutput.push_back("S");
                tempFIRSTOutput.push_back("T");
                tempFIRSTOutput.push_back("(");
                tempFIRSTOutput.push_back(nonTerm[i]);
                tempFIRSTOutput.push_back(")");
                tempFIRSTOutput.push_back(" ");
                tempFIRSTOutput.push_back("=");
                tempFIRSTOutput.push_back(" ");
                tempFIRSTOutput.push_back("{");
                tempFIRSTOutput.push_back(" ");

                //Get the position of epsilon in FIRST set
                for(int j = 0; j < universalOrderedTerminals.size(); j++)
                {
                    if(firstSet[i][j] == 1 && term[j] == "#")
                    {
                        epsilonIndex = j;
                        break;
                    }
                }

                if(epsilonIndex == -1)
                {
                    for(int j = 0; j < universalOrderedTerminals.size(); j++)
                    {
                        if(firstSet[i][j] == 1)
                        {
                            tempFIRSTOutput.push_back(term[j]);
                            tempFIRSTOutput.push_back(",");
                            tempFIRSTOutput.push_back(" ");
                        }
                    }
                    tempFIRSTOutput.push_back("}");
                    tempFIRSTOutput.push_back("\n");
                }
                else
                {
                    tempFIRSTOutput.push_back("#");
                    tempFIRSTOutput.push_back(",");
                    tempFIRSTOutput.push_back(" ");
                    for(int j = 0; j < universalOrderedTerminals.size(); j++)
                    {
                        if(firstSet[i][j] == 1)
                        {
                            if(j != epsilonIndex)
                            {
                                tempFIRSTOutput.push_back(term[j]);
                                tempFIRSTOutput.push_back(",");
                                tempFIRSTOutput.push_back(" ");
                            }
                            else
                            {
                                continue;
                            }
                        }
                    }
                    tempFIRSTOutput.push_back("}");
                    tempFIRSTOutput.push_back("\n");
                }
            }
        }
    }
}

void calculateFOLLOW()
{
    calculateFIRST();
    universalOrderedTerminals.push_back("$");

    int tempFOLLOW[100][100];

    for(int i = 0; i < universalOrderedNonTerminals.size(); i++)
    {
        for(int j = 0; j < universalOrderedTerminals.size(); j++)
        {
            tempFOLLOW[i][j] = 0;
        }
    }

    string nonTerm[universalOrderedNonTerminals.size()];
    string term[universalOrderedTerminals.size()];

    for(int i = 0; i < universalOrderedNonTerminals.size();i++)
    {
        nonTerm[i] = universalOrderedNonTerminals[i];
    }

    for(int i = 0; i < universalOrderedTerminals.size();i++)
    {
        term[i] = universalOrderedTerminals[i];
    }

    //Apply first rule of FOLLOW Sets => Start symbol has EOF in follow
    tempFOLLOW[index_Of(nonTerm,universalOrderedNonTerminals.size(),ruleList[0].LHS)][universalOrderedTerminals.size()-1] = 1;

    //Apply fourth rule of FOLLOW Sets
    for(auto rule : ruleList)
    {
        if(rule.RHS.size() > 1)
        {
            for(int i = 0; i < rule.RHS.size()-1; i++)
            {
                if(inNonTerminalList(rule.RHS[i]))
                {
                    if(inNonTerminalList(rule.RHS[i+1]))
                    {
                        //Add FIRST of RHS[i+1] to Follow of RHS[i]
                        for(int j = 0; j < universalOrderedTerminals.size()-1;j++)
                        {
                            if(firstSet[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[i+1])][j] == 1)
                            {
                                if(term[j] != "#")
                                {
                                    tempFOLLOW[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[i])][j] = 1;
                                }
                            }
                        }
                    }
                    else
                    {
                        tempFOLLOW[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[i])][index_Of(term,universalOrderedTerminals.size(),rule.RHS[i+1])] = 1;
                    }
                }
                else
                {
                    continue;
                }
            }
        }
    }

    //Applying fifth rule of FOLLOW Sets
    for(auto rule : ruleList)
    {
        if(rule.RHS.size() > 2)
        {
            for(int i = 0; i < rule.RHS.size()-2; i++)
            {
                if(inNonTerminalList(rule.RHS[i]))
                {
                    for(int i1 = i+1; i1 < rule.RHS.size()-1; i1++)
                    {
                        if(inNonTerminalList(rule.RHS[i1]))
                        {
                            if(firstSet[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[i1])][index_Of(term,universalOrderedTerminals.size()-1,"#")] == 1 )
                            {
                                //Add FIRST of RHS[i1+1] to follow of RHS[i]
                                if(inNonTerminalList(rule.RHS[i1+1]))
                                {
                                    for(int j = 0; j < universalOrderedTerminals.size()-1;j++)
                                    {
                                        if(firstSet[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[i1+1])][j] == 1)
                                        {
                                            if(term[j] != "#")
                                            {
                                                tempFOLLOW[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[i])][j] = 1;
                                            }
                                        }
                                    }
                                }
                                else
                                {
                                    tempFOLLOW[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[i])][index_Of(term,universalOrderedTerminals.size(),rule.RHS[i1+1])] = 1;
                                    break;
                                }
                            }
                            else
                            {
                                break;
                            }
                        }
                        else
                        {
                            break;
                        }
                    }
                }
                else
                {
                    continue;
                }
            }
        }
    }

    int FOLLOW[100][100];

    bool followAreEqual;
    do
    {
        followAreEqual = true;

        //Copy tempFollow to FOLLOW after each iteration
        for(int i = 0; i < universalOrderedNonTerminals.size() ; i++)
        {
            for(int j = 0; j < universalOrderedTerminals.size() ; j++)
            {
                FOLLOW[i][j] = tempFOLLOW[i][j];
            }
        }

        //Apply second rule of FOLLOW Sets
        for(auto rule : ruleList)
        {
            if(inNonTerminalList(rule.RHS[(rule.RHS.size()-1)]))
            {
                //Add follow of LHS to follow of last non terminal
                for(int i = 0; i < universalOrderedTerminals.size();i++)
                {
                    if(tempFOLLOW[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.LHS)][i] == 1)
                    {
                            tempFOLLOW[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[(rule.RHS.size()-1)])][i] = 1;
                    }
                }
            }
            else
            {
                continue;
            }
        }

        //Apply third rule of FOLLOW Sets
        for(auto rule : ruleList)
        {
            if(rule.RHS.size() > 1)
            {
                for(int i = (rule.RHS.size() - 1); i > 0 ; i--)
                {
                    if(inNonTerminalList(rule.RHS[i]))
                    {
                        if(firstSet[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[i])][index_Of(term,universalOrderedTerminals.size(),"#")] == 1)
                        {
                            if(inNonTerminalList(rule.RHS[i-1]))
                            {
                                //Add follow of LHS to follow of non terminal left to nullable non terminal
                                for(int j = 0; j < universalOrderedTerminals.size();j++)
                                {
                                    if(tempFOLLOW[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.LHS)][j] == 1)
                                    {
                                        tempFOLLOW[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[i-1])][j] = 1;
                                    }
                                }
                            }
                            else
                            {
                                break;
                            }
                        }
                        else
                        {
                            break;
                        }
                    }
                    else
                    {
                        break;
                    }
                }
            }
        }



        //Check if FOLLOW and tempFOLLOW are equal
        for(int i = 0; i < universalOrderedNonTerminals.size() ; i++)
        {
            for(int j = 0; j < universalOrderedTerminals.size() ; j++)
            {
                if(FOLLOW[i][j] != tempFOLLOW[i][j])
                {
                    followAreEqual = false;
                    break;
                }
            }
        }
    }while(!followAreEqual);

    //Copy FOLLOW to global FOLLOW Set
    for(int i = 0; i < universalOrderedNonTerminals.size(); i++)
    {
        for(int j = 0; j < universalOrderedTerminals.size(); j++)
        {
            followSet[i][j] = FOLLOW[i][j];
        }
    }
}

int main (int argc, char* argv[])
{
    int task;

    if (argc < 2)
    {
        cout << "Error: missing argument\n";
        return 1;
    }

    /*
       Note that by convention argv[0] is the name of your executable,
       and the first argument to your program is stored in argv[1]
     */
    task = atoi(argv[1]);

    // TODO: Read the input grammar at this point from standard input

    t = lexer.GetToken();
    while(t.token_type != DOUBLEHASH)
    {
        Rule r;

        r.LHS = t.lexeme;
        expect(ARROW);

        t = lexer.GetToken();

        if(t.token_type == HASH)
        {
            r.RHS.push_back("#");
            t = lexer.GetToken();
            ruleList.push_back(r);
            continue;
        }
        else if(t.token_type == ID)
        {
            while(t.token_type != HASH)
            {
                if(t.token_type == DOUBLEHASH)
                {
                    break;
                }
                r.RHS.push_back(t.lexeme);
                t = lexer.GetToken();
            }
            if(t.token_type == DOUBLEHASH)
            {
                ruleList.push_back(r);
                break;
            }
            else
            {
                ruleList.push_back(r);
                t = lexer.GetToken();
                continue;
            }
        }
        else if(t.token_type == DOUBLEHASH)
        {
            r.RHS.push_back("#");
            ruleList.push_back(r);
            break;
        }
        else
        {
            syntax_error();
        }
    }

    //Creating list of all the non-terminals
    for (auto rule : ruleList)
    {
        if(!inNonTerminalList(rule.LHS))
        {
            nonTerminals.push_back(rule.LHS);
        }
    }

    //Creating list of all the terminals
    for (auto rule : ruleList)
    {
        for(auto i : rule.RHS)
        {
            if(!inTerminalList(i) && !inNonTerminalList(i))
            {
                terminals.push_back(i);
            }
        }
    }

    vector<string> seen;

    //Sorting non-terminals in order
    for(auto rule : ruleList)
    {
        if(!(find(begin(seen), end(seen), rule.LHS) != end(seen)))
        {
            if(find(begin(nonTerminals), end(nonTerminals), rule.LHS) != end(nonTerminals))
            {
                seen.push_back(rule.LHS);
                orderedNonTerminals.push_back(rule.LHS);
                universalOrderedNonTerminals.push_back(rule.LHS);
            }
        }

        for(auto x : rule.RHS)
        {
            if(!(find(begin(seen), end(seen), x) != end(seen)))
            {
                if(find(begin(nonTerminals), end(nonTerminals), x) != end(nonTerminals))
                {
                    seen.push_back(x);
                    orderedNonTerminals.push_back(x);
                    universalOrderedNonTerminals.push_back(x);
                }
            }
        }
    }

    //Sorting terminals in order
    for(auto rule : ruleList)
    {
        for(auto x : rule.RHS)
        {
            if(!(find(begin(seen), end(seen), x) != end(seen)))
            {
                if(find(begin(terminals), end(terminals), x) != end(terminals))
                {
                    seen.push_back(x);
                    orderedTerminals.push_back(x);
                    universalOrderedTerminals.push_back(x);
                }
            }
        }
    }
    /*
       Hint: You can modify and use the lexer from previous project
       to read the input. Note that there are only 4 token types needed
       for reading the input in this project.

       WARNING: You will need to modify lexer.cc and lexer.h to only
       support the tokens needed for this project if you are going to
       use the lexer.
     */

    //This are will calculate the FIRST SET

    //The Code below is to calculate FOLLOW Sets

    switch (task) {
        case 1:
            {
                for(auto item : orderedNonTerminals)
                {
                    cout << item + " ";
                }
                for(auto item : orderedTerminals)
                {
                    if(item != "#")
                    {
                        cout << item + " ";
                    }
                }
            }
            break;

        case 2:
            {
                vector<Rule> tempRuleList;
                vector<Rule> finalRuleList;
                /*
                    This area is for creating the generating (true / false) array corresponding
                    to the terminals or non-terminals in grammar.
                */
                string allSymbolArray[nonTerminals.size() + terminals.size()];
                for(int i = 0; i < nonTerminals.size();i++)
                {
                    allSymbolArray[i] = nonTerminals[i];
                }

                int counter = 0;
                for(int i = nonTerminals.size(); i < (nonTerminals.size() + terminals.size());i++)
                {
                    allSymbolArray[i] = terminals[counter];
                    counter++;
                }

                int generatingArray[nonTerminals.size() + terminals.size()];
                for(int i = 0; i < nonTerminals.size();i++)
                {
                    generatingArray[i] = 0;
                }
                for(int i = nonTerminals.size(); i < (nonTerminals.size() + terminals.size());i++)
                {
                    generatingArray[i] = 1;
                }

                int tempArray[nonTerminals.size() + terminals.size()];
                copyIntegerArray(generatingArray,tempArray,(nonTerminals.size() + terminals.size()));

                do
                {
                    copyIntegerArray(tempArray,generatingArray,(nonTerminals.size() + terminals.size()));
                    for(auto rule : ruleList)
                    {
                        int product = 1;
                        for(auto i : rule.RHS)
                        {
                            product = product * tempArray[index_Of(allSymbolArray,(nonTerminals.size() + terminals.size()),i)];
                        }
                        if(product != 0)
                        {
                            tempArray[index_Of(allSymbolArray,(nonTerminals.size() + terminals.size()),rule.LHS)] = 1;
                        }
                    }

                }while(!intArrayAreEqual(tempArray,generatingArray,(nonTerminals.size() + terminals.size())));

                for(auto rule : ruleList)
                {
                    bool flag = true;
                    if(generatingArray[index_Of(allSymbolArray,nonTerminals.size(),rule.LHS)] == 1)
                    {
                        for(auto item : rule.RHS)
                        {
                            if(inNonTerminalList(item))
                            {
                                if(generatingArray[index_Of(allSymbolArray,nonTerminals.size(),item)] != 1)
                                {
                                    flag = false;
                                    break;
                                }
                            }
                        }
                    }
                    else
                    {
                        flag = false;
                    }
                    if(flag == true)
                    {
                        tempRuleList.push_back(rule);
                    }
                }
                /*
                    This area is for creating the reachable symbol (true / false) array corresponding
                    to the non-terminals in grammar.
                */
                int reachableSymbolArray[nonTerminals.size()];
                for(int i = 0; i < nonTerminals.size();i++)
                {
                    reachableSymbolArray[i] = 0;
                }
                //Set start symbol value to true as it is always reachable
                reachableSymbolArray[0] = 1;
                for(auto rule : tempRuleList)
                {
                    if(reachableSymbolArray[index_Of(allSymbolArray,nonTerminals.size(),rule.LHS)] == 1)
                    {
                        for(auto item : rule.RHS)
                        {
                            if(inNonTerminalList(item))
                            {
                                reachableSymbolArray[index_Of(allSymbolArray,nonTerminals.size(),item)] = 1;
                            }
                        }
                    }
                }

                for(auto rule : tempRuleList)
                {
                    bool flag = true;
                    if(reachableSymbolArray[index_Of(allSymbolArray,nonTerminals.size(),rule.LHS)] != 1)
                    {
                        flag = false;
                    }
                    if(flag)
                    {
                        finalRuleList.push_back(rule);
                    }
                }

                for(auto rule : finalRuleList)
                {
                    cout << rule.LHS + " " + "->" + " ";
                    for(auto item : rule.RHS)
                    {
                        cout << item + " ";
                    }
                    cout <<"\n";
                }
            }
            break;

        case 3:
            {
                calculateFIRST();
                vector<string> finalOutput;

                for(int i = 0 ; i < tempFIRSTOutput.size() - 2 ;i++)
                {
                    if(tempFIRSTOutput[i+2] == "}" && tempFIRSTOutput[i] == ",")
                    {
                        continue;
                    }
                    else
                    {
                        finalOutput.push_back(tempFIRSTOutput[i]);
                    }

                }
                finalOutput.push_back("}");

                for(int i = 0; i < finalOutput.size();i++)
                {
                    cout << finalOutput[i];
                }
            }
            break;

        case 4:
            {
                calculateFOLLOW();

                string nonTerm[universalOrderedNonTerminals.size()];
                string term[universalOrderedTerminals.size()];

                for(int i = 0; i < universalOrderedNonTerminals.size();i++)
                {
                    nonTerm[i] = universalOrderedNonTerminals[i];
                }

                for(int i = 0; i < universalOrderedTerminals.size();i++)
                {
                    term[i] = universalOrderedTerminals[i];
                }

                for(int i = 0; i < universalOrderedNonTerminals.size(); i++)
                {
                    int counter = 0;
                    cout << "FOLLOW(" + nonTerm[i] + ") = { ";

                    if(followSet[i][index_Of(term,universalOrderedTerminals.size(),"$")] == 1)
                    {
                        cout << "$";
                        counter++;
                    }

                    for(int j = 0 ; j < universalOrderedTerminals.size()-1;j++)
                    {
                        if(followSet[i][j] == 1)
                        {
                            if(counter == 0)
                            {
                                cout << term[j];
                                counter++;
                            }
                            else
                            {
                                cout << ", " + term[j];
                            }
                        }
                    }
                    cout << " }";
                    cout << "\n";
                }
            }
            break;

        case 5:
            {
                calculateFOLLOW();

                string nonTerm[universalOrderedNonTerminals.size()];
                string term[universalOrderedTerminals.size()];

                for(int i = 0; i < universalOrderedNonTerminals.size();i++)
                {
                    nonTerm[i] = universalOrderedNonTerminals[i];
                }

                for(int i = 0; i < universalOrderedTerminals.size();i++)
                {
                    term[i] = universalOrderedTerminals[i];
                }

                bool firstConditionIsTrue = true;
                for(int i = 0; i < universalOrderedNonTerminals.size();i++)
                {
                        vector<string> seen;
                        for(auto rule : ruleList)
                        {
                            if(rule.LHS == universalOrderedNonTerminals[i])
                            {
                                if(inNonTerminalList(rule.RHS[0]))
                                {
                                    for(int j = 0; j < universalOrderedTerminals.size()-1;j++)
                                    {
                                        if(firstSet[index_Of(nonTerm,universalOrderedNonTerminals.size(),rule.RHS[0])][j] == 1)
                                        {
                                            if(find(begin(seen), end(seen), term[j]) != end(seen))
                                            {
                                                firstConditionIsTrue = false;
                                                break;
                                            }
                                            else
                                            {
                                                seen.push_back(term[j]);
                                            }
                                        }
                                    }
                                }
                                else
                                {
                                    if(find(begin(seen), end(seen), rule.RHS[0]) != end(seen))
                                    {
                                        firstConditionIsTrue = false;
                                        break;
                                    }
                                    else
                                    {
                                        seen.push_back(rule.RHS[0]);
                                    }
                                }
                            }
                        }
                }

                if(firstConditionIsTrue)
                {
                    bool secondConditionIsTrue = true;

                    for(int i = 0; i < universalOrderedNonTerminals.size();i++)
                    {
                            if(firstSet[index_Of(nonTerm,universalOrderedNonTerminals.size(),universalOrderedNonTerminals[i])][index_Of(term,universalOrderedTerminals.size(),"#")] == 1)
                            {
                                vector<string> seen;
                                for(int j = 0 ; j < universalOrderedTerminals.size()-1; j++)
                                {
                                    if(firstSet[index_Of(nonTerm,universalOrderedNonTerminals.size(),universalOrderedNonTerminals[i])][j] == 1)
                                    {
                                        seen.push_back(term[j]);
                                    }
                                }

                                for(int j = 0 ; j < universalOrderedTerminals.size()-1; j++)
                                {
                                    if(followSet[index_Of(nonTerm,universalOrderedNonTerminals.size(),universalOrderedNonTerminals[i])][j] == 1)
                                    {
                                        if((find(begin(seen), end(seen), term[j]) != end(seen)))
                                        {
                                            secondConditionIsTrue = false;
                                            break;
                                        }
                                    }
                                }
                            }
                        }

                    if(firstConditionIsTrue == true && secondConditionIsTrue == true)
                    {
                        cout << "YES";
                    }
                    else
                    {
                        cout << "NO";
                    }
                }
                else
                {
                    cout << "NO";
                }
            }
            break;

        default:
            cout << "Error: unrecognized task number " << task << "\n";
            break;
    }
    return 0;
}

