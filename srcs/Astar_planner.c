#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#define MAX_NAME_LEN 25

typedef struct{
	char* general;
	char** types;
}Type;

typedef struct{
	char* name;
	char* type;
}Obj;

typedef struct{
	char* atom_name;
	char** argument;
	int arg_num;
}Atom;

typedef struct {
	char* func_name;
	char* argument;
	char* argument_type;
	int number;
}Func;

typedef struct {
  char *name;
  Atom *precond;
  int precond_num;
  Atom *neg_precond;
  int neg_precond_num;
  Atom *effect;
  int effect_num;
  Atom *neg_effect;
  int neg_effect_num;
  Atom *neg_cond;
  int neg_cond_num;
  Atom *cond;
  int cond_num;
  Atom *neg_cond_effect;
  Atom *cond_effect;
  int cost;
}Action;

typedef struct{
	char* atom_name;
	char** argument;
	int arg_num;
	int cost;
}H_atom;

typedef struct State{
	int state_num;
	int anum;
	Atom* curr_state;
	Action* possible_actions;
	int num_possible_actions;
	struct State* next_states;
	struct State* pred;
	int f;
	int h;
}State;

typedef struct State_cr{
	int state_num;
	Atom curr_state1;
	Atom curr_state2;
}State_cr;

void print_State (State the_state){
	printf("\n");
	printf("state_num: %d\n",the_state.state_num);
	printf("anum: %d\n",the_state.anum);
	printf("curr_state:\n");
	for(int i=0;i<the_state.anum;i++){
		printf("%s ",the_state.curr_state[i].atom_name);
		for(int j=0;j<the_state.curr_state[i].arg_num;j++){
			printf("%s ",the_state.curr_state[i].argument[j]);
		}
		printf("\n");
	}
	printf("num_possible_actions: %d\n",the_state.num_possible_actions);
	for(int i=0;i<the_state.num_possible_actions;i++){
		printf("%s\n",the_state.possible_actions[i].name);
	}
	for(int i=0;i<the_state.num_possible_actions;i++){
		printf("next_states[%d]=S%d\n",i,the_state.next_states[i].state_num);
		for(int j=0;j<the_state.next_states[i].anum;j++){
			printf("%s ",the_state.next_states[i].curr_state[j].atom_name);
			for(int k=0;k<the_state.next_states[i].curr_state[j].arg_num;k++){
				printf("%s ",the_state.next_states[i].curr_state[j].argument[k]);
			}
			printf("\n");
		}
	}
	if(the_state.pred!=NULL){
		printf("pred: S%d\n",the_state.pred->state_num);
	}
	else{
		printf("pred: no initialized\n");
	}
	printf("f: %d\n",the_state.f);
	printf("h: %d\n",the_state.h);
}

void search_possible_actions (int state_index, State* s_list, Action* a_list, int act_num){
	int cont1, cont2=0;
	int flag=0;
	for(int i=0;i<act_num;i++){
		cont2=a_list[i].precond_num;
		for(int j=0;j<a_list[i].precond_num;j++){
			for(int k=0;k<(s_list+state_index)->anum;k++){
				if(strcmp((s_list+state_index)->curr_state[k].atom_name,a_list[i].precond[j].atom_name)==0){
					if((s_list+state_index)->curr_state[k].arg_num!=0){
						cont1=(s_list+state_index)->curr_state[k].arg_num;
						for(int l=0;l<(s_list+state_index)->curr_state[k].arg_num;l++){
							if(strcmp((s_list+state_index)->curr_state[k].argument[l],a_list[i].precond[j].argument[l])==0){
								cont1--;
							}
						}
					}
					else{
						cont1=0;
					}
					if(cont1==0){
						//one argument is equal
						cont2--;
					}
				}
			}
		}
		flag=0;
		for(int j=0;j<a_list[i].neg_precond_num;j++){
			for(int k=0;k<(s_list+state_index)->anum;k++){
				if(strcmp((s_list+state_index)->curr_state[k].atom_name,a_list[i].neg_precond[j].atom_name)==0){
					if((s_list+state_index)->curr_state[k].arg_num==a_list[i].neg_precond[j].arg_num){
						cont1=(s_list+state_index)->curr_state[k].arg_num;
						for(int l=0;l<(s_list+state_index)->curr_state[k].arg_num;l++){
							if(strcmp((s_list+state_index)->curr_state[k].argument[l],a_list[i].neg_precond[j].argument[l])==0){
								cont1--;
							}
						}
					}
					else{
						cont1=0;
					}
					if(cont1==0){
						//one argument is equal
						flag=1;
					}
				}
			}
		}
		if(cont2==0&&flag==0){
			(s_list+state_index)->possible_actions[s_list[state_index].num_possible_actions]=a_list[i];
			s_list[state_index].num_possible_actions++;
		}
	}
}

void create_next_states (int state_index, State* s_list, Action* a_list, int act_num){
	int equal=0;
	(s_list+state_index)->next_states=malloc(((s_list+state_index)->num_possible_actions)*sizeof(State));
	for(int i=0;i<(s_list+state_index)->num_possible_actions;i++){
		(s_list+state_index)->next_states[i].curr_state = malloc((((s_list+state_index)->anum)+30)*sizeof(Atom));
		(s_list+state_index)->next_states[i].f =10000;
		(s_list+state_index)->next_states[i].h=0;
		(s_list+state_index)->next_states[i].anum = (s_list+state_index)->anum;
		//copy curr_state in all the next_states
		for(int j=0;j<(s_list+state_index)->anum;j++){
			(s_list+state_index)->next_states[i].curr_state[j].atom_name=malloc((strlen((s_list+state_index)->curr_state[j].atom_name))*sizeof(char));
			(s_list+state_index)->next_states[i].curr_state[j].argument=malloc(((s_list+state_index)->curr_state[j].arg_num)*sizeof(char*));
			(s_list+state_index)->next_states[i].curr_state[j].arg_num = (s_list+state_index)->curr_state[j].arg_num;
			strcpy((s_list+state_index)->next_states[i].curr_state[j].atom_name,(s_list+state_index)->curr_state[j].atom_name);
			for(int k=0;k<(s_list+state_index)->curr_state[j].arg_num;k++){
				(s_list+state_index)->next_states[i].curr_state[j].argument[k]=malloc((strlen((s_list+state_index)->curr_state[j].argument[k]))*sizeof(char));
				strcpy((s_list+state_index)->next_states[i].curr_state[j].argument[k],(s_list+state_index)->curr_state[j].argument[k]);
			}
		}
	}
	for (int j=0; j<(s_list+state_index)->num_possible_actions; j++) {
		for (int k=0; k<(s_list+state_index)->possible_actions[j].effect_num; k++) {
			for (int i=0; i<(s_list+state_index)->anum;i++) {
				if (strcmp((s_list+state_index)->curr_state[i].atom_name, (s_list+state_index)->possible_actions[j].effect[k].atom_name)==0) {
					for (int m=0; m<(s_list+state_index)->possible_actions[j].effect[k].arg_num; m++) {
						if (strcmp((s_list+state_index)->curr_state[i].argument[m], (s_list+state_index)->possible_actions[j].effect[k].argument[m])==0) {
							equal=1;
						}
						else {
							equal = 0;
							break;
						}
					}
					if (equal==1) {
						equal=0;
						break;
					}
					else if ((equal == 0)&&(i==(s_list+state_index)->anum-1)) {
						(s_list+state_index)->next_states[j].curr_state[(s_list+state_index)->next_states[j].anum].atom_name = malloc(strlen((s_list+state_index)->possible_actions[j].effect[k].atom_name)*sizeof(char));
						strcpy((s_list+state_index)->next_states[j].curr_state[(s_list+state_index)->next_states[j].anum].atom_name, (s_list+state_index)->possible_actions[j].effect[k].atom_name);
						(s_list+state_index)->next_states[j].curr_state[(s_list+state_index)->next_states[j].anum].argument = malloc(((s_list+state_index)->possible_actions[j].effect[k].arg_num)*sizeof(char*));
						for (int m=0; m<(s_list+state_index)->possible_actions[j].effect[k].arg_num; m++) {
							(s_list+state_index)->next_states[j].curr_state[(s_list+state_index)->next_states[j].anum].argument[m] =malloc((strlen((s_list+state_index)->possible_actions[j].effect[k].argument[m]))*sizeof(char));
							strcpy((s_list+state_index)->next_states[j].curr_state[(s_list+state_index)->next_states[j].anum].argument[m], (s_list+state_index)->possible_actions[j].effect[k].argument[m]);
						}
						(s_list+state_index)->next_states[j].curr_state[(s_list+state_index)->next_states[j].anum].arg_num = (s_list+state_index)->possible_actions[j].effect[k].arg_num;
						(s_list+state_index)->next_states[j].anum++;
					}
				}
				else {
					if(i==(s_list+state_index)->anum-1) {
						(s_list+state_index)->next_states[j].curr_state[(s_list+state_index)->next_states[j].anum].atom_name = malloc((strlen((s_list+state_index)->possible_actions[j].effect[k].atom_name))*sizeof(char));
						(s_list+state_index)->next_states[j].curr_state[(s_list+state_index)->next_states[j].anum].atom_name=(s_list+state_index)->possible_actions[j].effect[k].atom_name;
						(s_list+state_index)->next_states[j].curr_state[(s_list+state_index)->next_states[j].anum].argument =malloc(((s_list+state_index)->possible_actions[j].effect[k].arg_num)*sizeof(char*));
						for (int m=0; m<(s_list+state_index)->possible_actions[j].effect[k].arg_num; m++) {
							(s_list+state_index)->next_states[j].curr_state[(s_list+state_index)->next_states[j].anum].argument[m] =malloc((strlen((s_list+state_index)->possible_actions[j].effect[k].argument[m]))*sizeof(char));
							strcpy((s_list+state_index)->next_states[j].curr_state[(s_list+state_index)->next_states[j].anum].argument[m], (s_list+state_index)->possible_actions[j].effect[k].argument[m]);
						}
						(s_list+state_index)->next_states[j].curr_state[(s_list+state_index)->next_states[j].anum].arg_num = (s_list+state_index)->possible_actions[j].effect[k].arg_num;
						(s_list+state_index)->next_states[j].anum++;
					}
				}
			}
		}
	}
	equal=0;
	for (int j=0; j<(s_list+state_index)->num_possible_actions; j++) {
		for (int k=0; k<(s_list+state_index)->possible_actions[j].neg_effect_num; k++) {
			for (int i=0; i<(s_list+state_index)->next_states[j].anum;i++) {
				if (strcmp((s_list+state_index)->next_states[j].curr_state[i].atom_name, (s_list+state_index)->possible_actions[j].neg_effect[k].atom_name)==0) {
					equal=0;
					for (int m=0; m<(s_list+state_index)->possible_actions[j].neg_effect[k].arg_num; m++) {
						if (strcmp((s_list+state_index)->next_states[j].curr_state[i].argument[m], (s_list+state_index)->possible_actions[j].neg_effect[k].argument[m])==0) {
							equal = 1;
						}
						else {
							equal = 0;
							break;
						}
					}
					if (equal == 1) {

						for (int l=i; l<(s_list+state_index)->next_states[j].anum-1; l++) {
							(s_list+state_index)->next_states[j].curr_state[l].atom_name = malloc(strlen((s_list+state_index)->next_states[j].curr_state[l+1].atom_name)*sizeof(char));
							strcpy((s_list+state_index)->next_states[j].curr_state[l].atom_name, (s_list+state_index)->next_states[j].curr_state[l+1].atom_name);
							(s_list+state_index)->next_states[j].curr_state[l].arg_num = (s_list+state_index)->next_states[j].curr_state[l+1].arg_num;
							(s_list+state_index)->next_states[j].curr_state[l].argument = malloc((s_list+state_index)->next_states[j].curr_state[l].arg_num * sizeof(char*));
							for (int m=0; m<(s_list+state_index)->next_states[j].curr_state[l].arg_num; m++) {
								(s_list+state_index)->next_states[j].curr_state[l].argument[m] = malloc(strlen((s_list+state_index)->next_states[j].curr_state[l+1].argument[m])* sizeof(char));
								strcpy((s_list+state_index)->next_states[j].curr_state[l].argument[m], (s_list+state_index)->next_states[j].curr_state[l+1].argument[m]);
							}
						}
						(s_list+state_index)->next_states[j].anum--;
					}
				}
			}
		}
	}
}

int copy_next_states_if_new (int state_index, State* s_list, int index, int act_num){
	int equals[s_list[state_index].num_possible_actions];
	int i, j, k, l, m, n,counter=0, cont1=0, cont2, equal=0, flag=0;
	for (i=0;i<s_list[state_index].num_possible_actions;i++){
		equals[i]=2;
	}
	i=0;
	l=0;
	cont2=0;
	while(i<s_list[state_index].num_possible_actions){
		l=0;
		while(l<index){
			if(s_list[state_index].next_states[i].anum==(s_list+l)->anum){
				counter=(s_list+l)->anum;
				for(j=0;j<(s_list+l)->anum;j++){
					for(n=0;n<(s_list+l)->anum;n++){
						if(strcmp((s_list+state_index)->next_states[i].curr_state[j].atom_name,(s_list+l)->curr_state[n].atom_name)==0){
							cont1=(s_list+l)->curr_state[n].arg_num;
							for(k=0;k<(s_list+l)->curr_state[n].arg_num;k++){
								if(strcmp((s_list+state_index)->next_states[i].curr_state[j].argument[k],(s_list+l)->curr_state[n].argument[k])==0){
									cont1--;
								}
							}
							if(cont1==0){
								//atom is similar
								equal=1;
							}
							else{
								equal=0;
							}
						}
						if(equal==1){
							counter--;
						}
						equal=0;
					}
				}
				if(counter==0){
					//the state is equal
					s_list[state_index].next_states[i]=s_list[l];
					equals[i]=0;
					break;
				}
			}
			else if(l==(index-1)||s_list[state_index].next_states[i].anum!=(s_list+l)->anum){
				flag=1;

				equals[i]=1;
			}
			l++;
		}
		i++;
		cont2=index;
	}
	if(flag>0){
		for(l=0;l<s_list[state_index].num_possible_actions;l++){
			if(equals[l]==1){
				(s_list+index)->state_num=index;
				(s_list+index)->anum = (s_list+state_index)->next_states[l].anum;
				(s_list+index)->curr_state=malloc(((s_list+index)->anum)*sizeof(Atom));
				for (i=0; i<(s_list+index)->anum; i++) {
					(s_list+index)->curr_state[i].atom_name = malloc((strlen(s_list[state_index].next_states[l].curr_state[i].atom_name))*sizeof(char));
					strcpy((s_list+index)->curr_state[i].atom_name, (s_list+state_index)->next_states[l].curr_state[i].atom_name);
					(s_list+index)->curr_state[i].arg_num = s_list[state_index].next_states[l].curr_state[i].arg_num;
					(s_list+index)->curr_state[i].argument = malloc((s_list+index)->curr_state[i].arg_num*sizeof(char*));
					for (k=0; k<(s_list+index)->curr_state[i].arg_num; k++) {
						(s_list+index)->curr_state[i].argument[k] = malloc(strlen(s_list[state_index].next_states[l].curr_state[i].argument[k])*sizeof(char));
						strcpy((s_list+index)->curr_state[i].argument[k], s_list[state_index].next_states[l].curr_state[i].argument[k]);
					}
				}
				(s_list+index)->num_possible_actions=0;
				(s_list+index)->possible_actions=malloc(act_num*sizeof(Action));
				(s_list+index)->next_states=malloc(act_num*sizeof(State));
				(s_list+index)->pred=NULL;
				(s_list+index)->f=s_list[state_index].next_states[l].f;
				(s_list+index)->h=s_list[state_index].next_states[l].h;
				s_list[state_index].next_states[l]=s_list[index];
				index++;
			}
		}
	}
	return index;
}

void relaxation(Action* r_a_list, Action* a_list, int act_num) {
	int i, j, k;
	for (i=0; i<act_num; i++) {
		r_a_list[i].name = malloc(strlen(a_list[i].name)*sizeof(char));
		strcpy(r_a_list[i].name, a_list[i].name);
		r_a_list[i].precond_num = a_list[i].precond_num;
		r_a_list[i].precond = malloc(r_a_list[i].precond_num * sizeof(Atom));
		for (j=0; j<r_a_list[i].precond_num; j++) {
			r_a_list[i].precond[j].atom_name = malloc(strlen(a_list[i].precond[j].atom_name)*sizeof(char));
			strcpy(r_a_list[i].precond[j].atom_name, a_list[i].precond[j].atom_name);
			r_a_list[i].precond[j].arg_num = a_list[i].precond[j].arg_num;
			r_a_list[i].precond[j].argument = malloc(r_a_list[i].precond[j].arg_num * sizeof(char*));
			for (k=0; k<r_a_list[i].precond[j].arg_num; k++) {
				r_a_list[i].precond[j].argument[k] = malloc(strlen(a_list[i].precond[j].argument[k]) * sizeof(char));
				strcpy(r_a_list[i].precond[j].argument[k], a_list[i].precond[j].argument[k]);
			}
		}
		r_a_list[i].neg_precond_num = a_list[i].neg_precond_num;
		r_a_list[i].neg_precond = malloc(r_a_list[i].neg_precond_num * sizeof(Atom));
		for (j=0; j<r_a_list[i].neg_precond_num; j++) {
			r_a_list[i].neg_precond[j].atom_name = malloc(strlen(a_list[i].neg_precond[j].atom_name)*sizeof(char));
			strcpy(r_a_list[i].neg_precond[j].atom_name, a_list[i].neg_precond[j].atom_name);
			r_a_list[i].neg_precond[j].arg_num = a_list[i].neg_precond[j].arg_num;
			r_a_list[i].neg_precond[j].argument = malloc(r_a_list[i].neg_precond[j].arg_num * sizeof(char*));
			for (k=0; k<r_a_list[i].neg_precond[j].arg_num; k++) {
				r_a_list[i].neg_precond[j].argument[k] = malloc(strlen(a_list[i].neg_precond[j].argument[k]) * sizeof(char));
				strcpy(r_a_list[i].neg_precond[j].argument[k], a_list[i].neg_precond[j].argument[k]);
			}
		}
		r_a_list[i].effect_num = a_list[i].effect_num;
		r_a_list[i].effect = malloc(r_a_list[i].effect_num * sizeof(Atom));
		for (j=0; j<r_a_list[i].effect_num; j++) {
			r_a_list[i].effect[j].atom_name = malloc(strlen(a_list[i].effect[j].atom_name)*sizeof(char));
			strcpy(r_a_list[i].effect[j].atom_name, a_list[i].effect[j].atom_name);
			r_a_list[i].effect[j].arg_num = a_list[i].effect[j].arg_num;
			r_a_list[i].effect[j].argument = malloc(r_a_list[i].effect[j].arg_num * sizeof(char*));
			for (k=0; k<r_a_list[i].effect[j].arg_num; k++) {
				r_a_list[i].effect[j].argument[k] = malloc(strlen(a_list[i].effect[j].argument[k]) * sizeof(char));
				strcpy(r_a_list[i].effect[j].argument[k], a_list[i].effect[j].argument[k]);
			}
			r_a_list[i].neg_effect_num = 0;
		}
		r_a_list[i].cost = a_list[i].cost;
	}
}

int is_it_goal(State new_st, State goal_state) {
	int i;
	int m;
	int n;
	int equal = 0;
	int counter=0;
	for (i=0; i<goal_state.anum;i++) {
		for(m=0; m<new_st.anum; m++) {
			if (strcmp(new_st.curr_state[m].atom_name, goal_state.curr_state[i].atom_name)==0) {
				for(int n=0; n<new_st.curr_state[m].arg_num; n++) {
					if(strcmp(new_st.curr_state[m].argument[n], goal_state.curr_state[i].argument[n])==0) {
						equal=1;
					}
					else {
						equal=0;
						break;
					}
				}
				if(equal==1) {
					counter++;
					break;
				}
			}
		}
	}
	return (counter);
}

int is_it_goal_atom(State new_st, Atom goal_atom) {
	int i, j;
	int equal = 1;
	for(i=0; i<new_st.anum; i++) {
		if(strcmp(new_st.curr_state[i].atom_name, goal_atom.atom_name)==0) {
			for(j=0; j<new_st.curr_state[i].arg_num; j++) {
				if(strcmp(new_st.curr_state[i].argument[j], goal_atom.argument[j])==0) {
					equal = 1;
				}
				else {
					equal++;
					break;
				}
			}
			if(equal==1) {
				return(equal);
			}
		}
		else {
			equal++;
		}
	}
	return(equal);
}

int dr_heuristic(State my_state, Action* a_list, Atom goal_atom, int act_num) {
	int i, j, flag, index, bug=10000, not_copy;
	int nexts[bug];
	int f_in_nexts[bug];
	State *temp_list=NULL;
	temp_list=malloc(10000*sizeof(State));
	for(i=0;i<bug;i++){
		nexts[i]=0;
		f_in_nexts[i]=10000;
	}
	int sz_nexts=0;
	//copy the state we want to examine to the 1st place of  the temporary nexts' list
	temp_list[0].state_num = 0;
	temp_list[0].curr_state = malloc(my_state.anum*sizeof(Atom));
	temp_list[0].anum = my_state.anum;
	temp_list[0].f=0;
	temp_list[0].h=0;
	temp_list[0].pred = NULL;
	temp_list[0].num_possible_actions = 0;
	temp_list[0].possible_actions = malloc(act_num*sizeof(Action));
	temp_list[0].next_states = malloc(act_num*sizeof(Action));
	for (i=0; i<my_state.anum; i++) {
		temp_list[0].curr_state[i].atom_name = malloc(strlen(my_state.curr_state[i].atom_name)*sizeof(char));
		strcpy(temp_list[0].curr_state[i].atom_name, my_state.curr_state[i].atom_name);
		temp_list[0].curr_state[i].arg_num = my_state.curr_state[i].arg_num;
		temp_list[0].curr_state[i].argument = malloc(temp_list[0].curr_state[i].arg_num*(sizeof(char*)));
		for (j=0; j<temp_list[0].curr_state[i].arg_num; j++) {
			temp_list[0].curr_state[i].argument[j] = malloc(strlen(my_state.curr_state[i].argument[j])*sizeof(char));
			strcpy(temp_list[0].curr_state[i].argument[j], my_state.curr_state[i].argument[j]);
		}
	}
	flag=1;
	j=0;
	index=1;
	while(flag==1){
		if(temp_list[j].state_num==nexts[0]){
			if(is_it_goal_atom(temp_list[j], goal_atom)==1 && (j!=0)){
				return(temp_list[j].f);
			}
			else if ((is_it_goal_atom(temp_list[j], goal_atom)==1 && (j==0))) {
				return(0);
			}
			nexts[0]=0;
			f_in_nexts[0]=10000;
			if(sz_nexts!=0){
				for(int p=0;p<=index;p++){
					nexts[p]=nexts[p+1];
					f_in_nexts[p]=f_in_nexts[p+1];
				}
			}
			if (j==0) {
				search_possible_actions(j,temp_list,a_list,act_num);
				create_next_states(j,temp_list,a_list,act_num);
				index=copy_next_states_if_new(j,temp_list, 1,act_num);
			}
			else {
				search_possible_actions(j,temp_list,a_list,act_num);
				create_next_states(j,temp_list,a_list,act_num);
				index=copy_next_states_if_new(j,temp_list, index,act_num);
			}
			for(int k=0;k<temp_list[j].num_possible_actions;k++){
				for(int l=0;l<index;l++){
					if(temp_list[j].next_states[k].state_num==temp_list[l].state_num){
						if(temp_list[l].f>((temp_list[j].f)+(temp_list[j].possible_actions[k].cost))){
							temp_list[l].f=(temp_list[j].f)+(temp_list[j].possible_actions[k].cost);
							(temp_list+l)->pred=&(temp_list[j]);
							sz_nexts=0;
							for(int m=0;m<index;m++){
								if(f_in_nexts[m]!=10000){
									sz_nexts++;
								}
							}
							if (sz_nexts==0){
								nexts[0]=temp_list[l].state_num;
								f_in_nexts[0]=(temp_list[l].f);
							}
							else if (sz_nexts>0){
								for(int n=0;n<sz_nexts;n++){
									if ((((temp_list[l].f))<f_in_nexts[n])) {
										if (temp_list[l].state_num==nexts[n]) {
											nexts[n]=temp_list[l].state_num;
											f_in_nexts[n]=(temp_list[l].f)+(temp_list[l].h);
										}
										else {
											for(int p=sz_nexts;p>n-1;p--){
												nexts[p+1]=nexts[p];
												f_in_nexts[p+1]=f_in_nexts[p];
											}
											nexts[n]=temp_list[l].state_num;
											f_in_nexts[n]=(temp_list[l].f)+(temp_list[l].h);
										}
									}
									else if (((temp_list[l].f)>=f_in_nexts[n])&&(n==(sz_nexts-1))&&(temp_list[l].state_num!=nexts[n])){
										nexts[sz_nexts]=temp_list[l].state_num;
										f_in_nexts[sz_nexts]=(temp_list[l].f);
									}
								}
							}
						}
					}
				}
			}
		}
		else{
			if(j<index){
				j++;
			}
			else if(j==index){
				j=0;
			}
		}
		flag=0;
		for(i=0;i<bug;i++) {
			if(nexts[i]!=0) {
				flag=1;
			}
		}
	}
	printf("Goal atom not found!!\n");
	return(10000);

}

int factorial(int num){
	int i;
	for (i=num-1;i>=1;i--){
		num=num*i;
	}
	if(num==0)
	return 1;
	return num;
}

int num_combinations(int r, int n){
	int a;
	a=factorial(n)/(factorial(r)*factorial(n-r));
	return a;
}

int is_it_goal_2atom(State new_st, Atom goal_atom1, Atom goal_atom2) {
	if(is_it_goal_atom(new_st,goal_atom1)==1&&is_it_goal_atom(new_st,goal_atom2)==1){
		return 1;
	}
	else{
		return 0;
	}
}

int new_cr_heuristic (State my_state, Action* a_list, Atom goal_atom1, Atom goal_atom2, int act_num){
	int i, j, k, l, m, q, analysed;
	int cont, cont1;
	int index_cr=0, index_cr1=0, index, index1;
	int r = 2;
	int n;
	int *list_fin;
	State *temp_list=NULL;
	State_cr *temp_cr_list=NULL;
	temp_list=malloc(10000*sizeof(State));
	//copy my_state in temp_list[0]
	temp_list[0].state_num = 0;
	temp_list[0].curr_state = malloc(my_state.anum*sizeof(Atom));
	temp_list[0].anum = my_state.anum;
	temp_list[0].f=0;
	temp_list[0].h=0;
	temp_list[0].pred = NULL;
	temp_list[0].num_possible_actions = 0;
	temp_list[0].possible_actions = malloc(act_num*sizeof(Action));
	temp_list[0].next_states = malloc(act_num*sizeof(Action));
	for (i=0; i<my_state.anum; i++) {
		temp_list[0].curr_state[i].atom_name = malloc(strlen(my_state.curr_state[i].atom_name)*sizeof(char));
		strcpy(temp_list[0].curr_state[i].atom_name, my_state.curr_state[i].atom_name);
		temp_list[0].curr_state[i].arg_num = my_state.curr_state[i].arg_num;
		temp_list[0].curr_state[i].argument = malloc(temp_list[0].curr_state[i].arg_num*(sizeof(char*)));
		for (j=0; j<temp_list[0].curr_state[i].arg_num; j++) {
			temp_list[0].curr_state[i].argument[j] = malloc(strlen(my_state.curr_state[i].argument[j])*sizeof(char));
			strcpy(temp_list[0].curr_state[i].argument[j], my_state.curr_state[i].argument[j]);
		}
	}
	temp_cr_list=malloc(10000*sizeof(State_cr));
	index=1;
	index_cr=0;
	for(analysed=0;analysed<index;analysed++){
		if(temp_list[analysed].anum>=2){
			if(temp_list[analysed].anum>2){
				n=temp_list[analysed].anum;
				list_fin=malloc((num_combinations(r,n)*r)*(sizeof(int)));
				int i2=0;
				int j2=1;
				int k2=0;
				while(k2<(num_combinations(r,n)*r)){
					list_fin[k2]=i2;
					list_fin[k2+1]=j2;
					k2=k2+2;
					if(j2==n-1){
						i2++;
						j2=i2+1;
					}
					else{
						j2++;
					}
				}
				for(j=0;j<num_combinations(r,n)*r;j=j+r){
					//create a new state_cr with the combination of atoms in a curr_state
					//curr_state[j] in curr_state1
					temp_cr_list[index_cr].state_num=index_cr;
					temp_cr_list[index_cr].curr_state1.atom_name=malloc((strlen(temp_list[analysed].curr_state[list_fin[j]].atom_name))*sizeof(char));
					strcpy(temp_cr_list[index_cr].curr_state1.atom_name,temp_list[analysed].curr_state[list_fin[j]].atom_name);
					temp_cr_list[index_cr].curr_state1.arg_num=temp_list[analysed].curr_state[list_fin[j]].arg_num;
					temp_cr_list[index_cr].curr_state1.argument=malloc((temp_list[analysed].curr_state[list_fin[j]].arg_num)*sizeof(char*));
					for(k=0; k<temp_list[analysed].curr_state[list_fin[j]].arg_num;k++){
						temp_cr_list[index_cr].curr_state1.argument[k]=malloc((strlen(temp_list[analysed].curr_state[list_fin[j]].argument[k]))*sizeof(char));
						strcpy(temp_cr_list[index_cr].curr_state1.argument[k],temp_list[analysed].curr_state[list_fin[j]].argument[k]);
					}
					//curr_state[j+1] in curr_state2
					temp_cr_list[index_cr].curr_state2.atom_name=malloc((strlen(temp_list[analysed].curr_state[list_fin[j+1]].atom_name))*sizeof(char));
					strcpy(temp_cr_list[index_cr].curr_state2.atom_name,temp_list[analysed].curr_state[list_fin[j+1]].atom_name);
					temp_cr_list[index_cr].curr_state2.arg_num=temp_list[analysed].curr_state[list_fin[j+1]].arg_num;
					temp_cr_list[index_cr].curr_state2.argument=malloc((temp_list[analysed].curr_state[list_fin[j+1]].arg_num)*sizeof(char*));
					for(k=0; k<temp_list[analysed].curr_state[list_fin[j+1]].arg_num;k++){
						temp_cr_list[index_cr].curr_state2.argument[k]=malloc((strlen(temp_list[analysed].curr_state[list_fin[j+1]].argument[k]))*sizeof(char));
						strcpy(temp_cr_list[index_cr].curr_state2.argument[k],temp_list[analysed].curr_state[list_fin[j+1]].argument[k]);
					}
					index_cr++;
				}
			}
			else if(temp_list[analysed].anum==2){
				//curr_state[0] in curr_state1
				temp_cr_list[index_cr].state_num=index_cr;
				temp_cr_list[index_cr].curr_state1.atom_name=malloc((strlen(temp_list[analysed].curr_state[0].atom_name))*sizeof(char));
				strcpy(temp_cr_list[index_cr].curr_state1.atom_name,temp_list[analysed].curr_state[0].atom_name);
				temp_cr_list[index_cr].curr_state1.arg_num=temp_list[analysed].curr_state[0].arg_num;
				temp_cr_list[index_cr].curr_state1.argument=malloc((temp_list[analysed].curr_state[0].arg_num)*sizeof(char*));
				for(k=0; k<temp_list[analysed].curr_state[0].arg_num;k++){
					temp_cr_list[index_cr].curr_state1.argument[k]=malloc((strlen(temp_list[analysed].curr_state[0].argument[k]))*sizeof(char));
					strcpy(temp_cr_list[index_cr].curr_state1.argument[k],temp_list[analysed].curr_state[0].argument[k]);
				}
				//curr_state[1] in curr_state2
				temp_cr_list[index_cr].curr_state2.atom_name=malloc((strlen(temp_list[analysed].curr_state[1].atom_name))*sizeof(char));
				strcpy(temp_cr_list[index_cr].curr_state2.atom_name,temp_list[analysed].curr_state[1].atom_name);
				temp_cr_list[index_cr].curr_state2.arg_num=temp_list[analysed].curr_state[1].arg_num;
				temp_cr_list[index_cr].curr_state2.argument=malloc((temp_list[analysed].curr_state[1].arg_num)*sizeof(char*));
				for(k=0; k<temp_list[analysed].curr_state[1].arg_num;k++){
					temp_cr_list[index_cr].curr_state2.argument[k]=malloc((strlen(temp_list[analysed].curr_state[1].argument[k]))*sizeof(char));
					strcpy(temp_cr_list[analysed].curr_state2.argument[k],temp_list[analysed].curr_state[1].argument[k]);
				}
				index_cr++;
			}
			for(j=index_cr1;j<index_cr;j++){
				//search possible actions
				for(k=0;k<act_num;k++){
					if(a_list[k].neg_precond_num>0){
						cont1=0;
						for(l=0;l<a_list[k].neg_precond_num;l++){
							//search the neg_preconds
							if(strcmp(temp_cr_list[j].curr_state1.atom_name,a_list[k].neg_precond[l].atom_name)==0){
								cont=temp_cr_list[j].curr_state1.arg_num;
								for(m=0;m<temp_cr_list[j].curr_state1.arg_num;m++){
									if(strcmp(temp_cr_list[j].curr_state1.argument[m],a_list[k].neg_precond[l].argument[m])==0){
										cont--;
									}
								}
								if(cont==0){
									//curr_state1 is in the neg_precond
									cont1++;
								}
								else{
									//curr_state1 is not this neg_preconditions
									//see if curr_state2 it is in the neg_preconds
									if(strcmp(temp_cr_list[j].curr_state2.atom_name,a_list[k].neg_precond[l].atom_name)==0){
										cont=temp_cr_list[j].curr_state2.arg_num;
										for(q=0;q<temp_cr_list[j].curr_state2.arg_num;q++){
											if(strcmp(temp_cr_list[j].curr_state2.argument[q],a_list[k].neg_precond[l].argument[q])==0){
												cont--;
											}
										}
										if(cont==0){
											//curr_state2 is in the neg_preconditions
											cont1++;
										}
										else{
											//curr_state2 is not in the neg_preconditions
										}
									}
								}
							}
							else{
								//this neg_precond it is not in curr_state1
								//take a look on curr_state2
								if(strcmp(temp_cr_list[j].curr_state2.atom_name,a_list[k].neg_precond[l].atom_name)==0){
									cont=temp_cr_list[j].curr_state2.arg_num;
									for(q=0;q<temp_cr_list[j].curr_state2.arg_num;q++){
										if(strcmp(temp_cr_list[j].curr_state2.argument[q],a_list[k].neg_precond[l].argument[q])==0){
											cont--;
										}
									}
									if(cont==0){
										//curr_state2 is in the neg_preconditions
										cont1++;
									}
									else{
										//curr_state2 is not in the neg_preconditions
									}
								}
							}
						}
						if(cont1==0){
							//see the preconditions
							if(a_list[k].precond_num<=2){
								if(a_list[k].precond_num==2){
									for(l=0;l<a_list[k].precond_num;l++){
										if(strcmp(temp_cr_list[j].curr_state1.atom_name,a_list[k].precond[l].atom_name)==0){
											cont=temp_cr_list[j].curr_state1.arg_num;
											for(m=0;m<temp_cr_list[j].curr_state1.arg_num;m++){
												if(strcmp(temp_cr_list[j].curr_state1.argument[m],a_list[k].precond[l].argument[m])==0){
													cont--;
												}
											}
											if(cont==0){
												//curr_state1 is in the preconditions
												//see if curr_state2 is in the preconditions
												for(n=0;n<a_list[k].precond_num;n++){
													if(strcmp(temp_cr_list[j].curr_state2.atom_name,a_list[k].precond[n].atom_name)==0){
														cont=temp_cr_list[j].curr_state2.arg_num;
														for(q=0;q<temp_cr_list[j].curr_state2.arg_num;q++){
															if(strcmp(temp_cr_list[j].curr_state2.argument[q],a_list[k].precond[n].argument[q])==0){
																cont--;
															}
														}
														if(cont==0){
															//curr_state2 is in the preconditions
															temp_list[analysed].num_possible_actions++;
															temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
														}
														else{
															//curr_state2 is not in the preconditions
															//finish the loop
														}
													}
												}
											}
											else{
												//curr_state1 is not in the preconditions
												//finish the tour
											}
										}
									}
								}
								else if(a_list[k].precond_num==1){
									for(l=0;l<a_list[k].precond_num;l++){
										//see if curr_state1 is in the state
										if(strcmp(temp_cr_list[j].curr_state1.atom_name,a_list[k].precond[l].atom_name)==0){
											cont=temp_cr_list[j].curr_state1.arg_num;
											for(m=0;m<temp_cr_list[j].curr_state1.arg_num;m++){
												if(strcmp(temp_cr_list[j].curr_state1.argument[m],a_list[k].precond[l].argument[m])==0){
													cont--;
												}
											}
											if(cont==0){
												//curr_state1 is in the preconditions
												temp_list[analysed].num_possible_actions++;
												temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
											}
											else {
												for(n=0;n<a_list[k].precond_num;n++){
													if(strcmp(temp_cr_list[j].curr_state2.atom_name,a_list[k].precond[n].atom_name)==0){
														cont=temp_cr_list[j].curr_state2.arg_num;
														for(q=0;q<temp_cr_list[j].curr_state2.arg_num;q++){
															if(strcmp(temp_cr_list[j].curr_state2.argument[q],a_list[k].precond[n].argument[q])==0){
																cont--;
															}
														}
														if(cont==0){
															//curr_state2 is in the preconditions
															temp_list[analysed].num_possible_actions++;
															temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
														}
														else{
															//curr_state2 and curr_state1 are not in the preconditions
															//finish the loop
														}
													}
												}
											}
										}
									}
								}
								else if(a_list[k].precond_num==0){
									//the action is possible in any case
									temp_list[analysed].num_possible_actions++;
									temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
								}
							}
							else{
								//This action is not possible
							}
						}
						else{
							//some of the curr_state is in the neg_preconds
						}
					}
					else{
						//preconditions directly
						if(a_list[k].precond_num<=2){
							if(a_list[k].precond_num==2){
								for(l=0;l<a_list[k].precond_num;l++){
									if(strcmp(temp_cr_list[j].curr_state1.atom_name,a_list[k].precond[l].atom_name)==0){
										cont=temp_cr_list[j].curr_state1.arg_num;
										for(m=0;m<temp_cr_list[j].curr_state1.arg_num;m++){
											if(strcmp(temp_cr_list[j].curr_state1.argument[m],a_list[k].precond[l].argument[m])==0){
												cont--;
											}
										}
										if(cont==0){
											//curr_state1 is in the preconditions
											//see if curr_state2 is in the preconditions
											for(n=0;n<a_list[k].precond_num;n++){
												if(strcmp(temp_cr_list[j].curr_state2.atom_name,a_list[k].precond[n].atom_name)==0){
													cont=temp_cr_list[j].curr_state2.arg_num;
													for(q=0;q<temp_cr_list[j].curr_state2.arg_num;q++){
														if(strcmp(temp_cr_list[j].curr_state2.argument[q],a_list[k].precond[n].argument[q])==0){
															cont--;
														}
													}
													if(cont==0){
														//curr_state2 is in the preconditions
														temp_list[analysed].num_possible_actions++;
														temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
													}
													else{
														//curr_state2 is not in the preconditions
														//finish the loop
													}
												}
											}
										}
										else{
											//curr_state1 is not in the preconditions
											//finish the tour
										}
									}
								}
							}
							else if(a_list[k].precond_num==1){
								for(l=0;l<a_list[k].precond_num;l++){
									//see if curr_state1 is in the state
									if(strcmp(temp_cr_list[j].curr_state1.atom_name,a_list[k].precond[l].atom_name)==0){
										cont=temp_cr_list[j].curr_state1.arg_num;
										for(m=0;m<temp_cr_list[j].curr_state1.arg_num;m++){
											if(strcmp(temp_cr_list[j].curr_state1.argument[m],a_list[k].precond[l].argument[m])==0){
												cont--;
											}
										}
										if(cont==0){
											//curr_state1 is in the preconditions
											temp_list[analysed].num_possible_actions++;
											temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
										}
										else {
											for(n=0;n<a_list[k].precond_num;n++){
												if(strcmp(temp_cr_list[j].curr_state2.atom_name,a_list[k].precond[n].atom_name)==0){
													cont=temp_cr_list[j].curr_state2.arg_num;
													for(q=0;q<temp_cr_list[j].curr_state2.arg_num;q++){
														if(strcmp(temp_cr_list[j].curr_state2.argument[q],a_list[k].precond[n].argument[q])==0){
															cont--;
														}
													}
													if(cont==0){
														//curr_state2 is in the preconditions
														temp_list[analysed].num_possible_actions++;
														temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
													}
													else{
														//curr_state2 and curr_state1 are not in the preconditions
														//finish the loop
													}
												}
											}
										}
									}
								}
							}
							else if(a_list[k].precond_num==0){
								//the action is possible in any case
								temp_list[analysed].num_possible_actions++;
								temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
							}
						}
						else{
							//This action is not possible
						}
					}
				}
				//create new state in temp_list[1] with the result of the each possible action
				create_next_states(analysed,temp_list,a_list,act_num);
				index1=copy_next_states_if_new(analysed,temp_list,index,act_num);
				if(index1==index){
					//all the actions went to an already studied state
					//do nothing
				}
				else {
					//there are new states to study
					for(l=index;l<index1;l++){
						if(is_it_goal_2atom(temp_list[l],goal_atom1,goal_atom2)==1){
							temp_list[l].h=temp_list[analysed].h;
							return temp_list[l].h;
						}
						else{
							temp_list[l].h=temp_list[analysed].h+1;
						}
					}
					index=index1;
				}
			}
			index_cr1=index_cr;
		}
		else if(temp_list[analysed].anum==1){
			//copy the curr_state[0] in curr_state1. curr_state2 will not be used
			temp_cr_list[index_cr].state_num=index_cr;
			temp_cr_list[index_cr].curr_state1.atom_name=malloc((strlen(temp_list[analysed].curr_state[0].atom_name))*sizeof(char));
			strcpy(temp_cr_list[index_cr].curr_state1.atom_name,temp_list[analysed].curr_state[0].atom_name);
			temp_cr_list[index_cr].curr_state1.arg_num=temp_list[analysed].curr_state[0].arg_num;
			temp_cr_list[index_cr].curr_state1.argument=malloc((temp_list[analysed].curr_state[0].arg_num)*sizeof(char*));
			for(k=0; k<temp_list[analysed].curr_state[0].arg_num;k++){
				temp_cr_list[index_cr].curr_state1.argument[k]=malloc((strlen(temp_list[analysed].curr_state[0].argument[k]))*sizeof(char));
				strcpy(temp_cr_list[index_cr].curr_state1.argument[k],temp_list[analysed].curr_state[0].argument[k]);
			}
			index_cr++;
			for(j=index_cr1;j<index_cr;j++){
				//search possible actions
				for(k=0;k<act_num;k++){
					if(a_list[k].neg_precond_num>0){
						for(l=0;l<a_list[k].neg_precond_num;l++){
							if(strcmp(temp_cr_list[j].curr_state1.atom_name,a_list[k].neg_precond[l].atom_name)==0){
								cont=temp_cr_list[j].curr_state1.arg_num;
								for(m=0;m<temp_cr_list[j].curr_state1.arg_num;m++){
									if(strcmp(temp_cr_list[j].curr_state1.argument[m],a_list[k].neg_precond[l].argument[m])==0){
										cont--;
									}
								}
								if(cont==0){
									//curr_state1 is in the neg_precond, so this action is not possible
								}
								else{
									//curr_state1 is not in the neg_preconditions
									//search in the preconditions
									if(a_list[k].precond_num==1){
										for(l=0;l<a_list[k].precond_num;l++){
											//see if curr_state1 is in the state
											if(strcmp(temp_cr_list[j].curr_state1.atom_name,a_list[k].precond[l].atom_name)==0){
												cont=temp_cr_list[j].curr_state1.arg_num;
												for(m=0;m<temp_cr_list[j].curr_state1.arg_num;m++){
													if(strcmp(temp_cr_list[j].curr_state1.argument[m],a_list[k].precond[l].argument[m])==0){
														cont--;
													}
												}
												if(cont==0){
													//curr_state1 is in the preconditions
													temp_list[analysed].num_possible_actions++;
													temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
												}
												else {
													//curr_state1 is not in the preconditions, the action is not possible
												}
											}
										}
									}
									else if(a_list[k].precond_num==0){
										//the action is possible in any case
										temp_list[analysed].num_possible_actions++;
										temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
									}
									else{
										//This action is not possible
									}
								}
							}
							else{
								//this neg_precond is not curr_state1
							}
						}
					}
					else{
						//directly preconds
						if(a_list[k].precond_num==1){
							for(l=0;l<a_list[k].precond_num;l++){
								//see if curr_state1 is in the state
								if(strcmp(temp_cr_list[j].curr_state1.atom_name,a_list[k].precond[l].atom_name)==0){
									cont=temp_cr_list[j].curr_state1.arg_num;
									for(m=0;m<temp_cr_list[j].curr_state1.arg_num;m++){
										if(strcmp(temp_cr_list[j].curr_state1.argument[m],a_list[k].precond[l].argument[m])==0){
											cont--;
										}
									}
									if(cont==0){
										//curr_state1 is in the preconditions
										temp_list[analysed].num_possible_actions++;
										temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
									}
									else {
										//curr_state1 is not in the preconditions, the action is not possible
									}
								}
							}
						}
						else if(a_list[k].precond_num==0){
							//the action is possible in any case
							temp_list[analysed].num_possible_actions++;
							temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
						}
						else{
							//This action is not possible
						}
					}
				}
				//create new state in temp_list[1] with the result of the each possible action
				create_next_states(analysed,temp_list,a_list,act_num);
				index1=copy_next_states_if_new(analysed,temp_list,index,act_num);
				if(index1==index){
					//all the actions went to an already studied state
					//do nothing
				}
				else {
					//there are new states to study
					for(l=index;l<index1;l++){
						if(is_it_goal_2atom(temp_list[l],goal_atom1,goal_atom2)==1){
							temp_list[l].h=temp_list[analysed].h;
							return temp_list[l].h;
						}
						else{
							temp_list[l].h=temp_list[analysed].h+1;
						}
					}
					index=index1;
				}
			}
			index_cr1=index_cr;
		}
	}
	free(temp_cr_list);
	free(temp_list);
	return 10000;
}

int new_cr_heuristic_1goal(State my_state, Action* a_list, Atom goal_atom, int act_num){
	int i, j, k, l, m, q, analysed;
	int cont, cont1;
	int index_cr=0, index_cr1=0, index, index1;
	int r = 2;
	int n = my_state.anum;
	int *list_fin;
	State *temp_list=NULL;
	State_cr *temp_cr_list=NULL;
	temp_list=malloc(10000*sizeof(State));
	//copy my_state in temp_list[0]
	temp_list[0].state_num = 0;
	temp_list[0].curr_state = malloc(my_state.anum*sizeof(Atom));
	temp_list[0].anum = my_state.anum;
	temp_list[0].f=0;
	temp_list[0].h=0;
	temp_list[0].pred = NULL;
	temp_list[0].num_possible_actions = 0;
	temp_list[0].possible_actions = malloc(act_num*sizeof(Action));
	temp_list[0].next_states = malloc(act_num*sizeof(Action));
	for (i=0; i<my_state.anum; i++) {
		temp_list[0].curr_state[i].atom_name = malloc(strlen(my_state.curr_state[i].atom_name)*sizeof(char));
		strcpy(temp_list[0].curr_state[i].atom_name, my_state.curr_state[i].atom_name);
		temp_list[0].curr_state[i].arg_num = my_state.curr_state[i].arg_num;
		temp_list[0].curr_state[i].argument = malloc(temp_list[0].curr_state[i].arg_num*(sizeof(char*)));
		for (j=0; j<temp_list[0].curr_state[i].arg_num; j++) {
			temp_list[0].curr_state[i].argument[j] = malloc(strlen(my_state.curr_state[i].argument[j])*sizeof(char));
			strcpy(temp_list[0].curr_state[i].argument[j], my_state.curr_state[i].argument[j]);
		}
	}
	temp_cr_list=malloc(100*sizeof(State_cr));
	index=1;
	index_cr=0;
	for(analysed=0;analysed<index;analysed++){
		if(temp_list[analysed].anum>=2){
			if(temp_list[analysed].anum>2){
				n=temp_list[analysed].anum;
				list_fin=malloc((num_combinations(r,n)*r)*(sizeof(int)));
				int i2=0;
				int j2=1;
				int k2=0;
				while(k2<(num_combinations(r,n)*r)){
					list_fin[k2]=i2;
					list_fin[k2+1]=j2;
					k2=k2+2;
					if(j2==n-1){
						i2++;
						j2=i2+1;
					}
					else{
						j2++;
					}
				}
				for(j=0;j<num_combinations(r,n)*r;j=j+r){
					//create a new state_cr with the combination of atoms in a curr_state
					//curr_state[j] in curr_state1
					temp_cr_list[index_cr].state_num=index_cr;
					temp_cr_list[index_cr].curr_state1.atom_name=malloc((strlen(temp_list[analysed].curr_state[list_fin[j]].atom_name))*sizeof(char));
					strcpy(temp_cr_list[index_cr].curr_state1.atom_name,temp_list[analysed].curr_state[list_fin[j]].atom_name);
					temp_cr_list[index_cr].curr_state1.arg_num=temp_list[analysed].curr_state[list_fin[j]].arg_num;
					temp_cr_list[index_cr].curr_state1.argument=malloc((temp_list[analysed].curr_state[list_fin[j]].arg_num)*sizeof(char*));
					for(k=0; k<temp_list[analysed].curr_state[list_fin[j]].arg_num;k++){
						temp_cr_list[index_cr].curr_state1.argument[k]=malloc((strlen(temp_list[analysed].curr_state[list_fin[j]].argument[k]))*sizeof(char));
						strcpy(temp_cr_list[index_cr].curr_state1.argument[k],temp_list[analysed].curr_state[list_fin[j]].argument[k]);
					}
					//curr_state[j+1] in curr_state2
					temp_cr_list[index_cr].curr_state2.atom_name=malloc((strlen(temp_list[analysed].curr_state[list_fin[j+1]].atom_name))*sizeof(char));
					strcpy(temp_cr_list[index_cr].curr_state2.atom_name,temp_list[analysed].curr_state[list_fin[j+1]].atom_name);
					temp_cr_list[index_cr].curr_state2.arg_num=temp_list[analysed].curr_state[list_fin[j+1]].arg_num;
					temp_cr_list[index_cr].curr_state2.argument=malloc((temp_list[analysed].curr_state[list_fin[j+1]].arg_num)*sizeof(char*));
					for(k=0; k<temp_list[analysed].curr_state[list_fin[j+1]].arg_num;k++){
						temp_cr_list[index_cr].curr_state2.argument[k]=malloc((strlen(temp_list[analysed].curr_state[list_fin[j+1]].argument[k])+20)*sizeof(char));
						strcpy(temp_cr_list[index_cr].curr_state2.argument[k],temp_list[analysed].curr_state[list_fin[j+1]].argument[k]);
					}
					index_cr++;
				}
			}
			else if(temp_list[analysed].anum==2){
				temp_cr_list[index_cr].state_num=index_cr;
				temp_cr_list[index_cr].curr_state1.atom_name=malloc((strlen(temp_list[analysed].curr_state[0].atom_name))*sizeof(char));
				strcpy(temp_cr_list[index_cr].curr_state1.atom_name,temp_list[analysed].curr_state[0].atom_name);
				temp_cr_list[index_cr].curr_state1.arg_num=temp_list[analysed].curr_state[0].arg_num;
				temp_cr_list[index_cr].curr_state1.argument=malloc((temp_list[analysed].curr_state[0].arg_num)*sizeof(char*));
				for(k=0; k<temp_list[analysed].curr_state[0].arg_num;k++){
					temp_cr_list[index_cr].curr_state1.argument[k]=malloc((strlen(temp_list[analysed].curr_state[0].argument[k]))*sizeof(char));
					strcpy(temp_cr_list[index_cr].curr_state1.argument[k],temp_list[analysed].curr_state[0].argument[k]);
				}
				//curr_state[1] in curr_state2
				temp_cr_list[index_cr].curr_state2.atom_name=malloc((strlen(temp_list[analysed].curr_state[1].atom_name))*sizeof(char));
				strcpy(temp_cr_list[index_cr].curr_state2.atom_name,temp_list[analysed].curr_state[1].atom_name);
				temp_cr_list[index_cr].curr_state2.arg_num=temp_list[analysed].curr_state[1].arg_num;
				temp_cr_list[index_cr].curr_state2.argument=malloc((temp_list[analysed].curr_state[1].arg_num)*sizeof(char*));
				for(k=0; k<temp_list[analysed].curr_state[1].arg_num;k++){
					temp_cr_list[index_cr].curr_state2.argument[k]=malloc((strlen(temp_list[analysed].curr_state[1].argument[k]))*sizeof(char));
					strcpy(temp_cr_list[index_cr].curr_state2.argument[k],temp_list[analysed].curr_state[1].argument[k]);
				}
				index_cr++;
			}
			for(j=index_cr1;j<index_cr;j++){
				//search possible actions
				for(k=0;k<act_num;k++){
					if(a_list[k].neg_precond_num>0){
						cont1=0;
						for(l=0;l<a_list[k].neg_precond_num;l++){
							//search the neg_preconds
							if(strcmp(temp_cr_list[j].curr_state1.atom_name,a_list[k].neg_precond[l].atom_name)==0){
								cont=temp_cr_list[j].curr_state1.arg_num;
								for(m=0;m<temp_cr_list[j].curr_state1.arg_num;m++){
									if(strcmp(temp_cr_list[j].curr_state1.argument[m],a_list[k].neg_precond[l].argument[m])==0){
										cont--;
									}
								}
								if(cont==0){
									//curr_state1 is in the neg_precond
									cont1++;
								}
								else{
									//curr_state1 is not this neg_preconditions
									//see if curr_state2 it is in the neg_preconds
									if(strcmp(temp_cr_list[j].curr_state2.atom_name,a_list[k].neg_precond[l].atom_name)==0){
										cont=temp_cr_list[j].curr_state2.arg_num;
										for(q=0;q<temp_cr_list[j].curr_state2.arg_num;q++){
											if(strcmp(temp_cr_list[j].curr_state2.argument[q],a_list[k].neg_precond[l].argument[q])==0){
												cont--;
											}
										}
										if(cont==0){
											//curr_state2 is in the neg_preconditions
											cont1++;
										}
										else{
											//curr_state2 is not in the neg_preconditions
										}
									}
								}
							}
							else{
								//this neg_precond it is not in curr_state1
								//take a look on curr_state2
								if(strcmp(temp_cr_list[j].curr_state2.atom_name,a_list[k].neg_precond[l].atom_name)==0){
									cont=temp_cr_list[j].curr_state2.arg_num;
									for(q=0;q<temp_cr_list[j].curr_state2.arg_num;q++){
										if(strcmp(temp_cr_list[j].curr_state2.argument[q],a_list[k].neg_precond[l].argument[q])==0){
											cont--;
										}
									}
									if(cont==0){
										//curr_state2 is in the neg_preconditions
										cont1++;
									}
									else{
										//curr_state2 is not in the neg_preconditions
									}
								}
							}
						}
						if(cont1==0){
							//search the preconditions
							if(a_list[k].precond_num<=2){
								if(a_list[k].precond_num==2){
									for(l=0;l<a_list[k].precond_num;l++){
										if(strcmp(temp_cr_list[j].curr_state1.atom_name,a_list[k].precond[l].atom_name)==0){
											cont=temp_cr_list[j].curr_state1.arg_num;
											for(m=0;m<temp_cr_list[j].curr_state1.arg_num;m++){
												if(strcmp(temp_cr_list[j].curr_state1.argument[m],a_list[k].precond[l].argument[m])==0){
													cont--;
												}
											}
											if(cont==0){
												//curr_state1 is in the preconditions
												//see if curr_state2 is in the preconditions
												for(n=0;n<a_list[k].precond_num;n++){
													if(strcmp(temp_cr_list[j].curr_state2.atom_name,a_list[k].precond[n].atom_name)==0){
														cont=temp_cr_list[j].curr_state2.arg_num;
														for(q=0;q<temp_cr_list[j].curr_state2.arg_num;q++){
															if(strcmp(temp_cr_list[j].curr_state2.argument[q],a_list[k].precond[n].argument[q])==0){
																cont--;
															}
														}
														if(cont==0){
															//curr_state2 is in the preconditions
															temp_list[analysed].num_possible_actions++;
															temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
														}
														else{
															//curr_state2 is not in the preconditions
															//finish the loop
														}
													}
												}
											}
											else{
												//curr_state1 is not in the preconditions
												//finish the tour
											}
										}
									}
								}
								else if(a_list[k].precond_num==1){
									for(l=0;l<a_list[k].precond_num;l++){
										//see if curr_state1 is in the state
										if(strcmp(temp_cr_list[j].curr_state1.atom_name,a_list[k].precond[l].atom_name)==0){
											cont=temp_cr_list[j].curr_state1.arg_num;
											for(m=0;m<temp_cr_list[j].curr_state1.arg_num;m++){
												if(strcmp(temp_cr_list[j].curr_state1.argument[m],a_list[k].precond[l].argument[m])==0){
													cont--;
												}
											}
											if(cont==0){
												//curr_state1 is in the preconditions
												temp_list[analysed].num_possible_actions++;
												temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
											}
											else {
												for(n=0;n<a_list[k].precond_num;n++){
													if(strcmp(temp_cr_list[j].curr_state2.atom_name,a_list[k].precond[n].atom_name)==0){
														cont=temp_cr_list[j].curr_state2.arg_num;
														for(q=0;q<temp_cr_list[j].curr_state2.arg_num;q++){
															if(strcmp(temp_cr_list[j].curr_state2.argument[q],a_list[k].precond[n].argument[q])==0){
																cont--;
															}
														}
														if(cont==0){
															//curr_state2 is in the preconditions
															temp_list[analysed].num_possible_actions++;
															temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
														}
														else{
															//curr_state2 and curr_state1 are not in the preconditions
															//finish the loop
														}
													}
												}
											}
										}
									}
								}
								else if(a_list[k].precond_num==0){
									//the action is possible in any case
									temp_list[analysed].num_possible_actions++;
									temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
								}
							}
							else{
								//This action is not possible
							}
						}
					}
					else{
						//directly preconditions
						if(a_list[k].precond_num<=2){
							if(a_list[k].precond_num==2){
								for(l=0;l<a_list[k].precond_num;l++){
									if(strcmp(temp_cr_list[j].curr_state1.atom_name,a_list[k].precond[l].atom_name)==0){
										cont=temp_cr_list[j].curr_state1.arg_num;
										for(m=0;m<temp_cr_list[j].curr_state1.arg_num;m++){
											if(strcmp(temp_cr_list[j].curr_state1.argument[m],a_list[k].precond[l].argument[m])==0){
												cont--;
											}
										}
										if(cont==0){
											//curr_state1 is in the preconditions
											//see if curr_state2 is in the preconditions
											for(n=0;n<a_list[k].precond_num;n++){
												if(strcmp(temp_cr_list[j].curr_state2.atom_name,a_list[k].precond[n].atom_name)==0){
													cont=temp_cr_list[j].curr_state2.arg_num;
													for(q=0;q<temp_cr_list[j].curr_state2.arg_num;q++){
														if(strcmp(temp_cr_list[j].curr_state2.argument[q],a_list[k].precond[n].argument[q])==0){
															cont--;
														}
													}
													if(cont==0){
														//curr_state2 is in the preconditions
														temp_list[analysed].num_possible_actions++;
														temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
													}
													else{
														//curr_state2 is not in the preconditions
														//finish the loop
													}
												}
											}
										}
										else{
											//curr_state1 is not in the preconditions
											//finish the tour
										}
									}
								}
							}
							else if(a_list[k].precond_num==1){
								for(l=0;l<a_list[k].precond_num;l++){
									//see if curr_state1 is in the state
									if(strcmp(temp_cr_list[j].curr_state1.atom_name,a_list[k].precond[l].atom_name)==0){
										cont=temp_cr_list[j].curr_state1.arg_num;
										for(m=0;m<temp_cr_list[j].curr_state1.arg_num;m++){
											if(strcmp(temp_cr_list[j].curr_state1.argument[m],a_list[k].precond[l].argument[m])==0){
												cont--;
											}
										}
										if(cont==0){
											//curr_state1 is in the preconditions
											temp_list[analysed].num_possible_actions++;
											temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
										}
										else {
											for(n=0;n<a_list[k].precond_num;n++){
												if(strcmp(temp_cr_list[j].curr_state2.atom_name,a_list[k].precond[n].atom_name)==0){
													cont=temp_cr_list[j].curr_state2.arg_num;
													for(q=0;q<temp_cr_list[j].curr_state2.arg_num;q++){
														if(strcmp(temp_cr_list[j].curr_state2.argument[q],a_list[k].precond[n].argument[q])==0){
															cont--;
														}
													}
													if(cont==0){
														//curr_state2 is in the preconditions
														temp_list[analysed].num_possible_actions++;
														temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
													}
													else{
														//curr_state2 and curr_state1 are not in the preconditions
														//finish the loop
													}
												}
											}
										}
									}
								}
							}
							else if(a_list[k].precond_num==0){
								//the action is possible in any case
								temp_list[analysed].num_possible_actions++;
								temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
							}
						}
						else{
							//This action is not possible
						}
					}
				}
				//create new state in temp_list[1] with the result of the each possible action
				create_next_states(analysed,temp_list,a_list,act_num);
				index1=copy_next_states_if_new(analysed,temp_list,index,act_num);
				if(index1==index){
					//all the actions went to an already studied state
					//do nothing
				}
				else {
					//there are new states to study
					for(l=index;l<index1;l++){
						if(is_it_goal_atom(temp_list[l],goal_atom)==1){
							temp_list[l].h=temp_list[analysed].h;
							return temp_list[l].h;
						}
						else{
							temp_list[l].h=temp_list[analysed].h+1;
						}
					}
					index=index1;
				}
			}
			index_cr1=index_cr;
		}
		else if(temp_list[analysed].anum==1){
			//copy the curr_state[0] in curr_state1. curr_state2 will not be used
			temp_cr_list[index_cr].state_num=index_cr;
			temp_cr_list[index_cr].curr_state1.atom_name=malloc((strlen(temp_list[analysed].curr_state[0].atom_name))*sizeof(char));
			strcpy(temp_cr_list[index_cr].curr_state1.atom_name,temp_list[analysed].curr_state[0].atom_name);
			temp_cr_list[index_cr].curr_state1.arg_num=temp_list[analysed].curr_state[0].arg_num;
			temp_cr_list[index_cr].curr_state1.argument=malloc((temp_list[analysed].curr_state[0].arg_num)*sizeof(char*));
			for(k=0; k<temp_list[analysed].curr_state[0].arg_num;k++){
				temp_cr_list[index_cr].curr_state1.argument[k]=malloc((strlen(temp_list[analysed].curr_state[0].argument[k]))*sizeof(char));
				strcpy(temp_cr_list[index_cr].curr_state1.argument[k],temp_list[analysed].curr_state[0].argument[k]);
			}
			index_cr++;
			for(j=index_cr1;j<index_cr;j++){
				//search possible actions
				for(k=0;k<act_num;k++){
					if(a_list[k].neg_precond_num>0){
						if(strcmp(temp_cr_list[j].curr_state1.atom_name,a_list[k].neg_precond[0].atom_name)==0){
							cont=temp_cr_list[j].curr_state1.arg_num;
							for(m=0;m<temp_cr_list[j].curr_state1.arg_num;m++){
								if(strcmp(temp_cr_list[j].curr_state1.argument[m],a_list[k].neg_precond[0].argument[m])==0){
									cont--;
								}
							}
							if(cont==0){
								//curr_state1 is in the neg_precond, so this action is not possible
							}
							else{
								//curr_state1 is not in the neg_preconditions
								//search in the preconditions
								if(a_list[k].precond_num==1){
									for(l=0;l<a_list[k].precond_num;l++){
										//see if curr_state1 is in the state
										if(strcmp(temp_cr_list[j].curr_state1.atom_name,a_list[k].precond[l].atom_name)==0){
											cont=temp_cr_list[j].curr_state1.arg_num;
											for(m=0;m<temp_cr_list[j].curr_state1.arg_num;m++){
												if(strcmp(temp_cr_list[j].curr_state1.argument[m],a_list[k].precond[l].argument[m])==0){
													cont--;
												}
											}
											if(cont==0){
												//curr_state1 is in the preconditions
												temp_list[analysed].num_possible_actions++;
												temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
											}
											else {
												//curr_state1 is not in the preconditions, the action is not possible
											}
										}
									}
								}
								else if(a_list[k].precond_num==0){
									//the action is possible in any case
									temp_list[analysed].num_possible_actions++;
									temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
								}
								else{
									//This action is not possible
								}
							}
						}
						else{
							//this neg_precond is not curr_state1
							if(a_list[k].precond_num==1){
								for(l=0;l<a_list[k].precond_num;l++){
									//see if curr_state1 is in the state
									if(strcmp(temp_cr_list[j].curr_state1.atom_name,a_list[k].precond[l].atom_name)==0){
										cont=temp_cr_list[j].curr_state1.arg_num;
										for(m=0;m<temp_cr_list[j].curr_state1.arg_num;m++){
											if(strcmp(temp_cr_list[j].curr_state1.argument[m],a_list[k].precond[l].argument[m])==0){
												cont--;
											}
										}
										if(cont==0){
											//curr_state1 is in the preconditions
											temp_list[analysed].num_possible_actions++;
											temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
										}
										else {
											//curr_state1 is not in the preconditions, the action is not possible
										}
									}
								}
							}
							else if(a_list[k].precond_num==0){
								//the action is possible in any case
								temp_list[analysed].num_possible_actions++;
								temp_list[analysed].possible_actions[temp_list[analysed].num_possible_actions-1]=a_list[k];
							}
							else{
								//This action is not possible
							}
						}
					}
					else{
						//directly preconds
					}
				}
				//create new state in temp_list[1] with the result of the each possible action
				create_next_states(analysed,temp_list,a_list,act_num);
				index1=copy_next_states_if_new(analysed,temp_list,index,act_num);
				if(index1==index){
					//all the actions went to an already studied state
					//do nothing
				}
				else {
					//there are new states to study
					for(l=index;l<index1;l++){
						if(is_it_goal_atom(temp_list[l],goal_atom)==1){
							temp_list[l].h=temp_list[analysed].h;
							return temp_list[l].h;
						}
						else{
							temp_list[l].h=temp_list[analysed].h+1;
						}
					}
					index=index1;
				}
			}
			index_cr1=index_cr;
		}
	}
	free(temp_cr_list);
	free(temp_list);
	return 10000;
}

int main(int argc, char *argv[]) {
	int i=0, sz, j, k, l, m, flag,cont,cont1,cont2;
	int  objects_number=0, param_nb=0;
	char domain_finder[8], domain_finder2[9], init_finder[7], goal_finder[7];
	char constants_finder[12], predicate_finder[13], action_finder[9], types_finder[8];
	char objects_finder[10];
	char domain_name[MAX_NAME_LEN];
	char search[MAX_NAME_LEN];
	char stop_finder[4];
	int inf[]={0,0,0,0,0,0}, sup[]={0,0,0,0,0,0};
	Type *tType=NULL;
	int arg_num = 0;
	int type_num=0;
	int num=0;
	int typing=0;
	Obj *oObj = NULL;
	Obj *question = NULL;
	Atom *state = NULL;
	Atom *goal = NULL;
	int atom_num = 0;
	int fin=0;
	char *aname=NULL;
	char *arg_type[4];
	Atom *aAtom = NULL;
	char **combi = NULL;
	char **precond = NULL;
	Action *aAction = NULL;
	Action *relaxed_actions = NULL;
	State *states_list= NULL;
	int index;
	////////////////////////////////////////////////////////////////////////////
	//Open Domain and Problem Files
	////////////////////////////////////////////////////////////////////////////
	FILE* dom_ptr;
	FILE* p_ptr;
	for (j=0; j<8; j++) {
		domain_finder[j] = '\0';
	}
	for (j=0; j<9; j++) {
		domain_finder2[j] = '\0';
	}
	for (j=0; j<MAX_NAME_LEN; j++) {
		domain_name[j] = '\0';
	}
	if (argc != 3) {
		printf("Wrong number of Files\n");
		return (-1);
	}
	dom_ptr = fopen(argv[1], "r");
	if (dom_ptr == NULL) {
		printf("Fopen Error: Failed to open the Domain file");
		return (-1);
	}
	p_ptr = fopen(argv[2], "r");
	if (p_ptr == NULL) {
		printf("Fopen Error: Failed to open the %s file\n", argv[2]);
		return (-2);
	}
	////////////////////////////////////////////////////////////////////////////
	//Check Domain names
	////////////////////////////////////////////////////////////////////////////
	printf("\nChecking domain names... ");
	while (!feof(dom_ptr)) {
		fscanf(dom_ptr, "%s", domain_finder);
		if (strstr(domain_finder, "domain")!=0) {
			fscanf(dom_ptr, "%s", domain_name);
			int dom_name_sz = strlen(domain_name);
			char dname[dom_name_sz];
			strncpy(dname, domain_name, dom_name_sz-1);
			dname[dom_name_sz-1] = '\0';
			while (!feof(p_ptr)) {
				fscanf(p_ptr, "%s", domain_finder2);
				if (strstr(domain_finder2, "domain")!=0) {
					fscanf(p_ptr, "%s", domain_name);
					int dom_name_sz = strlen(domain_name);
					char pname[dom_name_sz];
					strncpy(pname, domain_name, dom_name_sz-1);
					pname[dom_name_sz-1] = '\0';
					printf("OK\n");
					if (strcmp(dname, pname)!=0) {
						printf("Different Domains!\n");
						return (-1);
					}
					break;
				}
			}
			break;
		}
	}
	////////////////////////////////////////////////////////////////////////////
	//Requirements check:
	//The pddl problems should obay to the PDDL fragment for IPC 2018
	//The pddl files should contain: STRIPS, action costs, negative preconditions
	//and conditional effects.
	//IF NOT PROCESS TERMINATES
	////////////////////////////////////////////////////////////////////////////
	fseek(dom_ptr, 0, SEEK_SET);
	printf("Checking the problem requirements...");
	while (!feof(dom_ptr)) {
		fscanf(dom_ptr, "%s", search);
		if ((strstr(search, "disjunctive-preconditions")!=0)||(strstr(search, "existential-preconditions")!=0)||(strstr(search, "universal-preconditions")!=0)||(strstr(search, "quantified-preconditions")!=0)||(strstr(search, "equality")!=0)||(strstr(search, "fluents")!=0)||(strstr(search, "durative-actions")!=0)||(strstr(search, "adl")!=0)||(strstr(search, "duration-inequalities")!=0)||(strstr(search, "continuous-effects")!=0)||(strstr(search, "derived-predicates")!=0)||(strstr(search, "timed-initial-literals")!=0)||(strstr(search, "preferences")!=0)||(strstr(search, "constraints")!=0)) {
			printf("\nIncompatible requirements of this pddl problem!Try another.\n");
			return(-1);
		}
	}
	printf("OK\n\n");
	////////////////////////////////////////////////////////////////////////////
	//Typing
	////////////////////////////////////////////////////////////////////////////
	for (int j=0; j<2; j++) {
		stop_finder[j] = '\0';
	}
	fseek(dom_ptr, 0, SEEK_SET);
	while(!feof(dom_ptr)) {
		fscanf(dom_ptr, "%s", types_finder);
		if (strstr(types_finder, "types")!=0) {
			typing=1;
			fscanf(dom_ptr, "%s", search);
			while (strstr(stop_finder, ")")==0) {
				if (strstr(stop_finder, "-")!=0) {
					fscanf(dom_ptr, "%s", search);
					type_num++;
				}
				fscanf(dom_ptr, "%s", search);
				strncpy(stop_finder, search, 3);
				stop_finder[3] = '\0';
			}
			break;
		}
	}
	tType = malloc((type_num)*sizeof(Type));
	fseek(dom_ptr, 0, SEEK_SET);
	for (int j=0; j<2; j++) {
		stop_finder[j] = '\0';
	}
	type_num=0;
	num=0;
	while(!feof(dom_ptr)) {
		fscanf(dom_ptr, "%s", types_finder);
		if (strstr(types_finder, "types")!=0) {
			fscanf(dom_ptr, "%s", search);
			while (strstr(stop_finder, ")")==0) {
				if (strstr(stop_finder, "-")!=0) {
					fscanf(dom_ptr, "%s", search);
					(tType+type_num)->types = (char**)malloc((num)*sizeof(char*));
					type_num++;
					num=0;
				}
				else {
					num++;
				}
				fscanf(dom_ptr, "%s", search);
				strncpy(stop_finder, search, 3);
				stop_finder[3] = '\0';
			}
			break;
		}
	}
	for (int j=0; j<2; j++) {
		stop_finder[j] = '\0';
	}
	fseek(dom_ptr, 0, SEEK_SET);
	type_num=0;
	num=0;
	while(!feof(dom_ptr)) {
		fscanf(dom_ptr, "%s", types_finder);
		if (strstr(types_finder, "types")!=0) {
			fscanf(dom_ptr, "%s", search);
			while (strstr(stop_finder, ")")==0) {
				if (strstr(stop_finder, "-")!=0) {
					fscanf(dom_ptr, "%s", search);
					sz = strlen(search);
					(tType+type_num)->general = malloc((sz+1)*sizeof(char));
					strcpy((tType+type_num)->general, search);
					strcpy((tType+type_num)->general+sz, "\0");
					type_num++;
					num=0;
				}
				else {
					sz=strlen(search);
					(tType+type_num)->types[num] = malloc((sz+1)*sizeof(char));
					strcpy((tType+type_num)->types[num], search);
					strcpy((tType+type_num)->types[num]+sz, "\0");
					num++;
				}
				fscanf(dom_ptr, "%s", search);
				strncpy(stop_finder, search, 3);
				stop_finder[3] = '\0';
			}
			break;
		}
	}
	////////////////////////////////////////////////////////////////////////////
	//Data Extraction
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	////////////////////////////////////////////////////////////////////////////
	//Constants & Objects
	////////////////////////////////////////////////////////////////////////////
	fseek(dom_ptr, 0, SEEK_SET);
	fseek(p_ptr, 0, SEEK_SET);
	for (int j=0; j<2; j++) {
		stop_finder[j] = '\0';
	}
	while (!feof(dom_ptr)) {
		fscanf(dom_ptr, "%s", constants_finder);
		if (strstr(constants_finder, "constants")!=0) {
			fscanf(dom_ptr, "%s", search);
			while (strstr(stop_finder, ")")==0) {
				if ((strstr(search, "-")!=0)&&(strlen(search)==1)) {
					fscanf(dom_ptr, "%s", search);
				}
				else {
					objects_number++;
				}
				fscanf(dom_ptr, "%s", search);
				strncpy(stop_finder, search, 3);
				stop_finder[3] = '\0';
			}
			break;
		}
	}
	for (int j=0; j<2; j++) {
		stop_finder[j] = '\0';
	}
	while (!feof(p_ptr)) {
		fscanf(p_ptr, "%s", objects_finder);
		if (strstr(objects_finder, "objects")!=0) {
			fscanf(p_ptr, "%s", search);
			while (strstr(search, ")")==0) {
				if (((strstr(search, "-")!=0)&&(strlen(search)==1))) {
					fscanf(p_ptr, "%s", search);
				}
				else {
					objects_number++;
				}
				fscanf(p_ptr, "%s", search);
			}
			if ((strstr(search, ")")!=0)&&(strlen(search)>1)) {
				objects_number++;
			}
			break;
		}
	}
	oObj = malloc(objects_number*sizeof(Obj));
	fseek(dom_ptr, 0, SEEK_SET);
	for (int j=0; j<2; j++) {
		stop_finder[j] = '\0';
	}
	sz=0;
	i=0;
	num=0;
	while (!feof(dom_ptr)) {
		fscanf(dom_ptr, "%s", constants_finder);
		if (strstr(constants_finder, "constants")!=0) {
			fscanf(dom_ptr, "%s", search);
			while (strstr(stop_finder, ")")==0) {
				if (((strstr(search, "-")!=0)&&(strlen(search)==1))) {
					fscanf(dom_ptr, "%s", search);
					sz = strlen(search);
					if(strstr(stop_finder, "(")!=0){
						for(l=0;l<sz;l++){
							search[l]=search[l+1];
						}
						sz--;
					}
					if(strstr(search,")")!=0){
						search[sz-1]="\0";
						sz--;
					}
					for (j=i-num; j<i; j++) {
						(oObj+j)->type = malloc((sz+1)*sizeof(char));
						strcpy((oObj+j)->type, search);
						strcpy((oObj+j)->type+sz, "\0");
					}
					num=0;
				}
				else {
					if (typing == 0) {
						sz = strlen(search);
						if(strstr(stop_finder, "(")!=0){
							for(l=0;l<sz;l++){
								search[l]=search[l+1];
							}
							sz--;
						}
						(oObj+i)->name = malloc((sz+1)*sizeof(char));
						strcpy((oObj+i)->name, search);
						strcpy((oObj+i)->name+sz, "\0");
						(oObj+i)->type = malloc(5*sizeof(char));
						strcpy((oObj+i)->type, "type");
						num++;
						i++;
					}
					else {
						sz = strlen(search);
						if(strstr(stop_finder, "(")!=0){
							for(l=0;l<sz;l++){
								search[l]=search[l+1];
							}
							sz--;
						}
						if(strstr(search,")")!=0){
							search[sz-1]="\0";
							sz--;
						}
						(oObj+i)->name = malloc((sz+1)*sizeof(char));
						strcpy((oObj+i)->name, search);
						strcpy((oObj+i)->name+sz, "\0");
						num++;
						i++;
					}
				}
				fscanf(dom_ptr, "%s", search);
				strncpy(stop_finder, search, 3);
				stop_finder[3] = '\0';
			}
			if ((strstr(search, ")")!=0)&&(strlen(search)>1)) {
				sz = strlen(search);
				if(strstr(stop_finder, "(")!=0){
					for(l=0;l<sz;l++){
						search[l]=search[l+1];
					}
					sz--;
				}
				if(strstr(search,")")!=0){
					search[sz-1]="\0";
					sz--;
				}
				(oObj+i)->name = malloc((sz+1)*sizeof(char));
				strcpy((oObj+i)->name, search);
				strcpy((oObj+i)->name+sz, "\0");
				(oObj+i)->type = malloc(5*sizeof(char));
				strcpy((oObj+i)->type, "type");
				num++;
				i++;
			}
			break;
		}
	}
	fseek(p_ptr, 0, SEEK_SET);
	for (int j=0; j<2; j++) {
		stop_finder[j] = '\0';
	}
	while (!feof(p_ptr)) {
		fscanf(p_ptr, "%s", objects_finder);
		if (strstr(objects_finder, "objects")!=0) {
			fscanf(p_ptr, "%s", search);
			while (strstr(stop_finder, ")")==0) {
				if (((strstr(search, "-")!=0)&&(strlen(search)==1))) {
					fscanf(p_ptr, "%s", search);
					sz = strlen(search);
					if(strstr(stop_finder, "(")!=0){
						for(l=0;l<sz;l++){
							search[l]=search[l+1];
						}
						sz--;
					}
					if(strstr(search,")")!=0){
						search[sz-1]="\0";
						sz--;
					}
					for (j=i-num; j<i; j++) {
						(oObj+j)->type = malloc((sz+1)*sizeof(char));
						strcpy((oObj+j)->type, search);
						strcpy((oObj+j)->type+sz, "\0");
					}
					num=0;
				}
				else {
					if (typing == 0) {
						sz = strlen(search);
						sz = strlen(search);
						if(strstr(stop_finder, "(")!=0){
							for(l=0;l<sz;l++){
								search[l]=search[l+1];
							}
							sz--;
						}
						if(strstr(search,")")!=0){
							search[sz-1]="\0";
							sz--;
						}
						(oObj+i)->name = malloc((sz+1)*sizeof(char));
						strcpy((oObj+i)->name, search);
						strcpy((oObj+i)->name+sz, "\0");
						(oObj+i)->type = malloc(5*sizeof(char));
						strcpy((oObj+i)->type, "type");
						num++;
						i++;
					}
					else {
						sz = strlen(search);
						if(strstr(stop_finder, "(")!=0){
							for(l=0;l<sz;l++){
								search[l]=search[l+1];
							}
							sz--;
						}
						if(strstr(search,")")!=0){
							search[sz-1]="\0";
							sz--;
						}
						(oObj+i)->name = malloc((sz+1)*sizeof(char));
						strcpy((oObj+i)->name, search);
						strcpy((oObj+i)->name+sz, "\0");
						i++;
						num++;
					}
				}
				fscanf(p_ptr, "%s", search);
				strncpy(stop_finder, search, 3);
				stop_finder[3] = '\0';
			}
			if ((strstr(search, ")")!=0)&&(strlen(search)>1)) {
				sz = strlen(search);
				if(strstr(search,")")!=0){
					search[sz-1]="\0";
					sz--;
				}
				(oObj+i)->name = malloc((sz)*sizeof(char));
				strncpy((oObj+i)->name, search, sz);
				strcpy((oObj+i)->name+sz, "\0");
				(oObj+i)->type = malloc(5*sizeof(char));
				strcpy((oObj+i)->type, "type");
				num++;
				i++;
			}
			break;
		}
	}

	////////////////////////////////////////////////////////////////////////////
	//predicates
	////////////////////////////////////////////////////////////////////////////
	int arg_sz=0;
	fseek(dom_ptr, 0, SEEK_SET);
	for (int j=0; j<2; j++) {
		stop_finder[j] = '\0';
	}
	for (int j=0; j<MAX_NAME_LEN; j++) {
		search[j] = '\0';
	}
	for (j=0; j<4; j++) {
		arg_type[j] = malloc(sizeof(char));
		strcpy(arg_type[j], "\0");
	}
	while (!feof(dom_ptr)) {
		fscanf(dom_ptr, "%s", predicate_finder);
		if (strstr(predicate_finder, "predicates")!=0) {
			fscanf(dom_ptr, "%s", search);
			while (strstr(stop_finder, "(:")==0) {
				if (strstr(stop_finder, "?")!=0) {
					if (typing == 1) {
						if (strstr(stop_finder, ")")==0) {
							fscanf(dom_ptr, "%s", search);
							if ((strstr(search, "-")!=0)&&(strlen(search)==1)) {
								fscanf(dom_ptr, "%s", search);
								sz=strlen(search);
								arg_type[arg_num] = malloc((sz+1)*sizeof(char));
								strcpy(arg_type[arg_num], search);
								strcpy(arg_type[arg_num]+sz, "\0");
							}
							else {
								fseek(dom_ptr, -strlen(search), SEEK_CUR);
							}
							arg_num++;
						}
						while (strstr(search, ")")==0) {
							fscanf(dom_ptr, "%s", search);
							if (strstr(search, "?")!=0) {
								fscanf(dom_ptr, "%s", search);
								if ((strstr(search, "-")!=0)&&(strlen(search)==1)) {
									fscanf(dom_ptr, "%s", search);
									sz=strlen(search);
									arg_type[arg_num] = malloc((sz+1)*sizeof(char));
									strcpy(arg_type[arg_num], search);
									strcpy(arg_type[arg_num]+sz, "\0");
									for (k=0; k<arg_num; k++) {
										if (strlen(arg_type[k])==0) {
											arg_type[k] = malloc((sz+1)*sizeof(char));
											strcpy(arg_type[k], arg_type[arg_num]);
											strcpy(arg_type[k]+sz, "\0");
										}
									}
								}
								else {
									fseek(dom_ptr, -strlen(search), SEEK_CUR);
								}
								arg_num++;
							}
						}
						sz=strlen(search);
						fseek(dom_ptr, -(sz+3), SEEK_CUR);
						fscanf (dom_ptr, "%s", search);
						fin = 1;
					}
					else {
						if (strstr(search, ")")!=0) {
							fin = 1;

						}
						else {
							fin = 0;
						}
						arg_type[arg_num] = malloc((5)*sizeof(char));
						strcpy(arg_type[arg_num], "type");
						for (k=0; k<arg_num; k++) {
							if (strlen(arg_type[k])==0) {
								arg_type[arg_num] = malloc((5)*sizeof(char));
								strcpy(arg_type[arg_num], "type");
							}
						}
						arg_num++;
					}
				}
				if (((strstr(search, "-")!=0)&&(strlen(search)==1))||(fin==1)) {
					if (arg_num==1) {
						for(i=0; i<objects_number; i++) {
							if ((strstr(arg_type[0], (oObj+i)->type)!=0)&&(strlen(arg_type[0])>1)) {
								atom_num++;
							}
						}
					}
					else if (arg_num==2) {
						for (i=0; i<objects_number; i++) {
							for (j=0; j<objects_number; j++) {
								if (i!=j) {
									if (((strstr(arg_type[0], (oObj+i)->type)!=0)&&(strlen(arg_type[0])>1))&&((strstr(arg_type[1], (oObj+j)->type)!=0)&&(strlen(arg_type[1])>1))) {
										atom_num++;
									}
								}
							}
						}
					}
					else if (arg_num == 3) {
						for (i=0; i<objects_number; i++) {
							for (j=0; j<objects_number; j++) {
								for (k=0; k<objects_number; k++) {
									if ((i!=j)&&(i!=k)&&(j!=k)) {
										if (((strstr(arg_type[0], (oObj+i)->type)!=0)&&(strlen(arg_type[0])>1))&&((strstr(arg_type[1], (oObj+j)->type)!=0)&&(strlen(arg_type[1])>1))&&((strstr(arg_type[2], (oObj+k)->type)!=0)&&(strlen(arg_type[2])>1))) {
											atom_num++;
										}
									}
								}
							}
						}
					}
					else if(arg_num==4) {
						for (i=0; i<objects_number; i++) {
							for (j=0; j<objects_number; j++) {
								for (k=0; k<objects_number; k++) {
									for (l=0; l<objects_number; l++) {
										if ((i!=j)&&(i!=k)&&(i!=l)&&(j!=k)&&(j!=l)&&(k!=l)) {
											if (((strstr(arg_type[0], (oObj+i)->type)!=0)&&(strlen(arg_type[0])>1))&&((strstr(arg_type[1], (oObj+j)->type)!=0)&&(strlen(arg_type[1])>1))&&((strstr(arg_type[2], (oObj+k)->type)!=0)&&(strlen(arg_type[2])>1))&&((strstr(arg_type[3], (oObj+l)->type)!=0)&&(strlen(arg_type[3])>1))) {
												atom_num++;
											}
										}
									}
								}
							}
						}
					}
					arg_num=0;
					fin=0;
					if (typing == 1) {
						fscanf(dom_ptr, "%s", search);
					}
					for (j=0; j<4; j++) {
						sz=strlen(arg_type[j]);
						for (k=0; k<sz; k++) {
							strcpy(arg_type[j]+k, "\0");
						}
					}
				}
				else if (strstr(search, "?")==0) {
					if (strstr(search, ")")!=0) {
						atom_num++;
					}
				}
				fscanf(dom_ptr, "%s", search);
				strncpy(stop_finder, search, 3);
				stop_finder[3] = '\0';
			}
			break;
		}
	}
	aAtom = malloc((sizeof(Atom))*(atom_num));
	for (j=0; j<4; j++) {
		arg_type[j] = malloc(sizeof(char));
		strcpy(arg_type[j], "\0");
	}
	fseek(dom_ptr, 0, SEEK_SET);
	fin = 0;
	atom_num = 0;
	arg_num=0;
	for (int j=0; j<2; j++) {
		stop_finder[j] = '\0';
	}
	for (int j=0; j<MAX_NAME_LEN; j++) {
		search[j] = '\0';
	}
	while (!feof(dom_ptr)) {
		fscanf(dom_ptr, "%s", predicate_finder);
		if (strstr(predicate_finder, "predicates")!=0) {
			fscanf(dom_ptr, "%s", search);
			while (strstr(search, "(:")==0) {
				if (strstr(search, "?")!=0) {
					if (typing == 1) {
						if (strstr(search, ")")==0) {
							fscanf(dom_ptr, "%s", search);
							if ((strstr(search, "-")!=0)&&(strlen(search)==1)) {
								fscanf(dom_ptr, "%s", search);
								sz=strlen(search);
								arg_type[arg_num] = malloc((sz+1)*sizeof(char));
								strcpy(arg_type[arg_num], search);
								strcpy(arg_type[arg_num]+sz, "\0");
							}
							else {
								fseek(dom_ptr, -strlen(search), SEEK_CUR);
							}
							arg_num++;
						}
						while (strstr(search, ")")==0) {
							fscanf(dom_ptr, "%s", search);
							if (strstr(search, "?")!=0) {
								fscanf(dom_ptr, "%s", search);
								if ((strstr(search, "-")!=0)&&(strlen(search)==1)) {
									fscanf(dom_ptr, "%s", search);
									sz=strlen(search);
									arg_type[arg_num] = malloc((sz+1)*sizeof(char));
									strcpy(arg_type[arg_num], search);
									strcpy(arg_type[arg_num]+sz, "\0");
									for (k=0; k<arg_num; k++) {
										if (strlen(arg_type[k])==0) {
											arg_type[k] = malloc((sz+1)*sizeof(char));
											strcpy(arg_type[k], arg_type[arg_num]);
											strcpy(arg_type[k]+sz, "\0");
										}
									}
								}
								else {
									fseek(dom_ptr, -strlen(search), SEEK_CUR);
								}
								arg_num++;
							}
						}
						sz=strlen(search);
						fseek(dom_ptr, -(sz+3), SEEK_CUR);
						fscanf (dom_ptr, "%s", search);
						fin = 1;
					}
					else {
						if (strstr(search, ")")!=0) {
							fin = 1;
						}
						else {
							fin = 0;
						}
						arg_type[arg_num] = malloc((5)*sizeof(char));
						strcpy(arg_type[arg_num], "type");
						for (k=0; k<arg_num; k++) {
							if (strlen(arg_type[k])==0) {
								arg_type[arg_num] = malloc((5)*sizeof(char));
								strcpy(arg_type[arg_num], "type");
							}
						}
						arg_num++;
					}
				}
				if (((strstr(search, "-")!=0)&&(strlen(search)==1))||(fin==1)) {
					if (arg_num==1) {
						for(i=0; i<objects_number; i++) {
							if ((strstr(arg_type[0], (oObj+i)->type)!=0)&&(strlen(arg_type[0])>1)) {
								(aAtom+atom_num)->argument = (char**)malloc(sizeof(char*));
								atom_num++;
							}
						}
					}
					else if (arg_num==2) {
						for (i=0; i<objects_number; i++) {
							for (j=0; j<objects_number; j++) {
								if (i!=j) {
									if (((strstr(arg_type[0], (oObj+i)->type)!=0)&&(strlen(arg_type[0])>1))&&((strstr(arg_type[1], (oObj+j)->type)!=0)&&(strlen(arg_type[1])>1))) {
										(aAtom+atom_num)->argument = (char**)malloc(2*sizeof(char*));
										atom_num++;
									}
								}
							}
						}
					}
					else if (arg_num == 3) {
						for (i=0; i<objects_number; i++) {
							for (j=0; j<objects_number; j++) {
								for (k=0; k<objects_number; k++) {
									if ((i!=j)&&(i!=k)&&(j!=k)) {
										if (((strstr(arg_type[0], (oObj+i)->type)!=0)&&(strlen(arg_type[0])>1))&&((strstr(arg_type[1], (oObj+j)->type)!=0)&&(strlen(arg_type[1])>1))&&((strstr(arg_type[2], (oObj+k)->type)!=0)&&(strlen(arg_type[2])>1))) {
											(aAtom+atom_num)->argument = (char**)malloc(3*sizeof(char*));
											atom_num++;
										}
									}
								}
							}
						}
					}
					else if(arg_num==4) {
						for (i=0; i<objects_number; i++) {
							for (j=0; j<objects_number; j++) {
								for (k=0; k<objects_number; k++) {
									for (l=0; l<objects_number; l++) {
										if ((i!=j)&&(i!=k)&&(i!=l)&&(j!=k)&&(j!=l)&&(k!=l)) {
											if (((strstr(arg_type[0], (oObj+i)->type)!=0)&&(strlen(arg_type[0])>1))&&((strstr(arg_type[1], (oObj+j)->type)!=0)&&(strlen(arg_type[1])>1))&&((strstr(arg_type[2], (oObj+k)->type)!=0)&&(strlen(arg_type[2])>1))&&((strstr(arg_type[3], (oObj+l)->type)!=0)&&(strlen(arg_type[3])>1))) {
												(aAtom+atom_num)->argument = (char**)malloc(4*sizeof(char*));
												atom_num++;
											}
										}
									}
								}
							}
						}
					}
					arg_num=0;
					fin=0;
					if (typing == 1) {
						fscanf(dom_ptr, "%s", search);
					}
					for (j=0; j<4; j++) {
						sz=strlen(arg_type[j]);
						for (k=0; k<sz; k++) {
							strcpy(arg_type[j]+k, "\0");
						}
					}
				}
				else if (strstr(search, "?")==0) {
					if (strstr(search, ")")!=0) {
						atom_num++;
					}
				}
				fscanf(dom_ptr, "%s", search);
				strncpy(stop_finder, search, 3);
				stop_finder[3] = '\0';
			}
			break;
		}
	}
	fin = 0;
	atom_num = 0;
	fseek(dom_ptr, 0, SEEK_SET);
	arg_num=0;
	for (j=0; j<2; j++) {
		stop_finder[j] = '\0';
	}
	for (j=0; j<4; j++) {
		arg_type[j] = malloc(sizeof(char));
		strcpy(arg_type[j], "\0");
	}
	while (!feof(dom_ptr)) {
		fscanf(dom_ptr, "%s", predicate_finder);
		if (strstr(predicate_finder, "predicates")!=0) {
			fscanf(dom_ptr, "%s", search);
			while (strstr(search, "(:")==0) {
				if (strstr(search, "?")!=0) {
					if (typing == 1) {
						if (strstr(search, ")")==0) {
							fscanf(dom_ptr, "%s", search);
							if ((strstr(search, "-")!=0)&&(strlen(search)==1)) {
								fscanf(dom_ptr, "%s", search);
								sz=strlen(search);
								arg_type[arg_num] = malloc((sz+1)*sizeof(char));
								strcpy(arg_type[arg_num], search);
								strcpy(arg_type[arg_num]+sz, "\0");
							}
							else {
								fseek(dom_ptr, -strlen(search), SEEK_CUR);
							}
							arg_num++;
						}
						while (strstr(search, ")")==0) {
							fscanf(dom_ptr, "%s", search);
							if (strstr(search, "?")!=0) {
								fscanf(dom_ptr, "%s", search);
								if ((strstr(search, "-")!=0)&&(strlen(search)==1)) {
									fscanf(dom_ptr, "%s", search);
									sz=strlen(search);
									arg_type[arg_num] = malloc((sz+1)*sizeof(char));
									strcpy(arg_type[arg_num], search);
									strcpy(arg_type[arg_num]+sz, "\0");
									for (k=0; k<arg_num; k++) {
										if (strlen(arg_type[k])==0) {
											arg_type[k] = malloc((sz+1)*sizeof(char));
											strcpy(arg_type[k], arg_type[arg_num]);
											strcpy(arg_type[k]+sz, "\0");
										}
									}
								}
								else {
									fseek(dom_ptr, -strlen(search), SEEK_CUR);
								}
								arg_num++;
							}
							fin = 0;
						}
						sz=strlen(search);
						fseek(dom_ptr, -(sz+3), SEEK_CUR);
						fscanf (dom_ptr, "%s", search);
						fin = 1;
					}
					else {
						if (strstr(search, ")")!=0) {
							fin = 1;
						}
						else {
							fin = 0;
						}
						arg_type[arg_num] = malloc((5)*sizeof(char));
						strcpy(arg_type[arg_num], "type");
						for (k=0; k<arg_num; k++) {
							if (strlen(arg_type[k])!=4) {
								arg_type[k] = malloc((5)*sizeof(char));
								strcpy(arg_type[arg_num], "type");
							}
						}
						arg_num++;
					}
				}
				if (((strstr(search, "-")!=0)&&(strlen(search)==1))||(fin==1)) {
					if (arg_num==1) {  //if 1 argument
						for(i=0; i<objects_number; i++) {
							if ((strstr(arg_type[0], (oObj+i)->type)!=0)&&(strlen(arg_type[0])>1)) {
								sz=strlen(aname);
								(aAtom+atom_num)->atom_name = malloc((sz+1)*(sizeof(char)));
								strcpy((aAtom+atom_num)->atom_name, aname);
								strcpy((aAtom+atom_num)->atom_name+sz, "\0");
								arg_sz = strlen((oObj+i)->name);
								(aAtom+atom_num)->argument[0] = malloc((arg_sz+1)*sizeof(char));
								strcpy((aAtom+atom_num)->argument[0], (oObj+i)->name);
								strcpy((aAtom+atom_num)->argument[0]+arg_sz, "\0");
								(aAtom+atom_num)->arg_num = 1;
								atom_num++;
							}
						}
					}
					else if (arg_num==2) {
						for (i=0; i<objects_number; i++) {
							for (j=0; j<objects_number; j++) {
								if (i!=j) {
									if (((strstr(arg_type[0], (oObj+i)->type)!=0)&&(strlen(arg_type[0])>1))&&((strstr(arg_type[1], (oObj+j)->type)!=0)&&(strlen(arg_type[1])>1))) {
										sz=strlen(aname);
										(aAtom+atom_num)->atom_name = malloc((sz+1)*(sizeof(char)));
										strcpy((aAtom+atom_num)->atom_name, aname);
										strcpy((aAtom+atom_num)->atom_name+sz, "\0");
										arg_sz = strlen((oObj+i)->name);
										(aAtom+atom_num)->argument[0] = malloc((arg_sz+1)*sizeof(char));
										strcpy((aAtom+atom_num)->argument[0], (oObj+i)->name);
										strcpy((aAtom+atom_num)->argument[0]+arg_sz, "\0");
										arg_sz = strlen((oObj+j)->name);
										(aAtom+atom_num)->argument[1] = malloc((arg_sz+1)*sizeof(char));
										strcpy((aAtom+atom_num)->argument[1], (oObj+j)->name);
										strcpy((aAtom+atom_num)->argument[1]+arg_sz, "\0");
										(aAtom+atom_num)->arg_num = 2;
										atom_num++;
									}
								}
							}
						}
					}
					else if (arg_num==3) {
						for (i=0; i<objects_number; i++) {
							for (j=0; j<objects_number; j++) {
								for (k=0; k<objects_number; k++) {
									if ((i!=j)&&(i!=k)&&(j!=k)) {
										if (((strstr(arg_type[0], (oObj+i)->type)!=0)&&(strlen(arg_type[0])>1))&&((strstr(arg_type[1], (oObj+j)->type)!=0)&&(strlen(arg_type[1])>1))&&((strstr(arg_type[2], (oObj+k)->type)!=0)&&(strlen(arg_type[2])>1))) {
											sz=strlen(aname);
											(aAtom+atom_num)->atom_name = malloc((sz+1)*(sizeof(char)));
											strcpy((aAtom+atom_num)->atom_name, aname);
											strcpy((aAtom+atom_num)->atom_name+sz, "\0");
											arg_sz = strlen((oObj+i)->name);
											(aAtom+atom_num)->argument[0] = malloc((arg_sz+1)*sizeof(char));
											strcpy((aAtom+atom_num)->argument[0], (oObj+i)->name);
											strcpy((aAtom+atom_num)->argument[0]+arg_sz, "\0");
											arg_sz = strlen((oObj+j)->name);
											(aAtom+atom_num)->argument[1] = malloc((arg_sz+1)*sizeof(char));
											strcpy((aAtom+atom_num)->argument[1], (oObj+j)->name);
											strcpy((aAtom+atom_num)->argument[1]+arg_sz, "\0");
											arg_sz = strlen((oObj+k)->name);
											(aAtom+atom_num)->argument[2] = malloc((arg_sz+1)*sizeof(char));
											strcpy((aAtom+atom_num)->argument[2], (oObj+k)->name);
											strcpy((aAtom+atom_num)->argument[2]+arg_sz, "\0");
											(aAtom+atom_num)->arg_num = 3;
											atom_num++;
										}
									}
								}
							}
						}
					}
					else if(arg_num==4) {
						for (i=0; i<objects_number; i++) {
							for (j=0; j<objects_number; j++) {
								for (k=0; k<objects_number; k++) {
									for (l=0; l<objects_number; l++) {
										if ((i!=j)&&(i!=k)&&(i!=l)&&(j!=k)&&(j!=l)&&(k!=l)) {
											if (((strstr(arg_type[0], (oObj+i)->type)!=0)&&(strlen(arg_type[0])>1))&&((strstr(arg_type[1], (oObj+j)->type)!=0)&&(strlen(arg_type[1])>1))&&((strstr(arg_type[2], (oObj+k)->type)!=0)&&(strlen(arg_type[2])>1))&&((strstr(arg_type[3], (oObj+l)->type)!=0)&&(strlen(arg_type[3])>1))) {
												sz=strlen(aname);
												(aAtom+atom_num)->atom_name = malloc((sz+1)*(sizeof(char)));
												strcpy((aAtom+atom_num)->atom_name, aname);
												strcpy((aAtom+atom_num)->atom_name+sz, "\0");
												arg_sz = strlen((oObj+i)->name);
												(aAtom+atom_num)->argument[0] = malloc((arg_sz+1)*sizeof(char));
												strcpy((aAtom+atom_num)->argument[0], (oObj+i)->name);
												strcpy((aAtom+atom_num)->argument[0]+arg_sz, "\0");
												arg_sz = strlen((oObj+j)->name);
												(aAtom+atom_num)->argument[1] = malloc((arg_sz+1)*sizeof(char));
												strcpy((aAtom+atom_num)->argument[1], (oObj+j)->name);
												strcpy((aAtom+atom_num)->argument[1]+arg_sz, "\0");
												arg_sz = strlen((oObj+k)->name);
												(aAtom+atom_num)->argument[2] = malloc((arg_sz+1)*sizeof(char));
												strcpy((aAtom+atom_num)->argument[2], (oObj+k)->name);
												strcpy((aAtom+atom_num)->argument[2]+arg_sz, "\0");
												arg_sz = strlen((oObj+l)->name);
												(aAtom+atom_num)->argument[3] = malloc((arg_sz+1)*sizeof(char));
												strcpy((aAtom+atom_num)->argument[3], (oObj+l)->name);
												strcpy((aAtom+atom_num)->argument[3]+arg_sz, "\0");
												(aAtom+atom_num)->arg_num = 4;
												atom_num++;
											}
										}
									}
								}
							}
						}
					}
					arg_num=0;
					fin = 0;
					if (typing == 1) {
						fscanf(dom_ptr, "%s", search);
					}
					for (j=0; j<4; j++) {
						sz=strlen(arg_type[j]);
						for (k=0; k<sz; k++) {
							strcpy(arg_type[j]+k, "\0");
						}
					}
				}
				else if (strstr(search, "?")==0){
					sz = strlen(search);
					aname = malloc((sz+1)*sizeof(char));
					strcpy(aname, search);
					strcpy(aname+sz, "\0");
					if (strstr(search,")")!=0) {
						sz=strlen(aname);
						(aAtom+atom_num)->atom_name = malloc((sz+1)*(sizeof(char)));
						strcpy((aAtom+atom_num)->atom_name, aname);
						strcpy((aAtom+atom_num)->atom_name+sz, "\0");
						(aAtom+atom_num)->arg_num = 0;
						atom_num++;
					}
				}
				fscanf(dom_ptr, "%s", search);
				strncpy(stop_finder, search, 3);
				stop_finder[3] = '\0';
			}
			break;
		}
	}
	///////////////////////////////////////////////////////
	//Actions
	///////////////////////////////////////////////////////
	int max = 1000;
	aAction = malloc(max*sizeof(Action));
	for (i=0;i<max; i++) {
	  aAction[i].precond = malloc(20*sizeof(Atom));
	  aAction[i].precond_num = 0;
	  aAction[i].neg_precond = malloc(20*sizeof(Atom));
	  aAction[i].neg_precond_num = 0;
	  aAction[i].effect = malloc(20*sizeof(Atom));
	  aAction[i].effect_num = 0;
	  aAction[i].neg_effect = malloc(20*sizeof(Atom));
	  aAction[i].neg_effect_num = 0;
	  aAction[i].neg_cond = malloc(20*sizeof(Atom));
	  aAction[i].neg_cond_num = 0;
	  aAction[i].cond = malloc(20*sizeof(Atom));
	  aAction[i].cond_num = 0;
	  aAction[i].neg_cond_effect = malloc(40*sizeof(Atom));
	  aAction[i].cond_effect = malloc(40*sizeof(Atom));
	  for (j=0; j<20; j++) {
	    aAction[i].precond[j].argument = (char**)malloc(3000*sizeof(char*));
	    aAction[i].neg_precond[j].argument = (char**)malloc(3000*sizeof(char*));
	    aAction[i].effect[j].argument = (char**)malloc(3000*sizeof(char*));
	    aAction[i].neg_effect[j].argument = (char**)malloc(3000*sizeof(char*));
	  }
	}
	int r=0;
	int neg_indicator = 0;
	int neg_num = 0;
	int pos_num = 0;
	int cond_num=0;
	int cond_indicator=0;
	char* action_name = malloc(1000*sizeof(char));
  int cost;
  m=0;
  j=0;
  k=0;
  int act_num=0;
  param_nb=0;
  question = malloc(50*sizeof(Obj));

  fseek(dom_ptr, 0, SEEK_SET);
  while (!feof(dom_ptr)) {
    fscanf(dom_ptr, "%s", action_finder);
    if (strstr(action_finder, "(:action")!=0) {
      fscanf(dom_ptr, "%s", search);
      if(strstr(search,")")!=0){
        search[sz-1]="\0";
        sz--;
      }
      strcpy(action_name, search);

      while (strstr(stop_finder, ":pr")==0) {
        if (strstr(search, ":parameters")!=0||j==1) {
          j=1;
          if (strstr(stop_finder, "?")!=0) {
            sz=strlen(search);
            if(strstr(stop_finder, "(")!=0){
              for(l=0;l<sz;l++){
                search[l]=search[l+1];
              }
              sz--;
            }
            (question+m)->name = malloc((sz+1)*sizeof(char));
            if(strstr(search,")")!=0){
              search[sz-1]="\0";
              sz--;
            }
            strcpy((question+m)->name, search);
            strcpy((question+m)->name+sz, "\0");
            if(typing == 0) {
              (question+m)->type = malloc((5)*sizeof(char));
              strcpy((question+m)->type, "type");
            }
            m++;
            param_nb++;
          }
          else if(strstr(stop_finder, "-")==0&&strstr(stop_finder, ":pa")==0){
            sz=strlen(search);
            if(strstr(search, ")")!=0){
              search[sz]="\0";
              sz--;
            }
            (question+k)->type = malloc((sz+1)*sizeof(char));
            strcpy((question+k)->type, search);
            strcpy((question+k)->type+sz, "\0");
            k++;
          }
        }
        fscanf(dom_ptr, "%s", search);
        strncpy(stop_finder, search, 3);
        stop_finder[3] = '\0';
      }
      if (typing==1) {
  	    if(k!=m){
  		      for(i=k;i<m;i++){
  			         (question+i)->type= (question+k-1)->type;
  		      }
        }
      }
      k=0;
      j=0;
      int p_num=0;

      fscanf(dom_ptr, "%s", search);
      combi = (char**)malloc(100*sizeof(char*)); //stores the combination of param_nb constants to substitute in parameters
      flag=0;
      for(i=0;i<param_nb;i++){
        for (j=0; j<objects_number; j++){
          if(strstr((question+i)->type,(oObj+j)->type)!=0&&flag==0){
            inf[i]=j;
            sup[i]=j;
            flag=1;
          }
          else if (strstr((question+i)->type,(oObj+j)->type)!=0&&flag==1){
            sup[i]=j;
          }
        }
        flag=0;
      }
	  cont=0;
      for(i=inf[0];i<=sup[0];i++){ //create all the combinations of param_nb elements and store them in combi
        if(sup[1]!=0){
          for(j=inf[1];j<=sup[1];j++){
            if(sup[2]!=0){
              for(k=inf[2];k<=sup[2];k++){
                if(sup[3]!=0){
                  for(l=inf[3];l<=sup[3];l++){
                    if(sup[4]!=0){
                      for(int n=inf[4];n<=sup[4];n++){
                        if(sup[5]!=0){
                          for(m=inf[5];m<=sup[5];m++){
                            if((strstr((oObj+i)->name, (oObj+j)->name)==0)&&(strstr((oObj+i)->name, (oObj+k)->name)==0)&&(strstr((oObj+j)->name, (oObj+k)->name)==0)&&(strstr((oObj+i)->name, (oObj+l)->name)==0)&&(strstr((oObj+j)->name, (oObj+l)->name)==0)&&(strstr((oObj+k)->name, (oObj+l)->name)==0)&&(strstr((oObj+i)->name, (oObj+n)->name)==0)&&(strstr((oObj+j)->name, (oObj+n)->name)==0)&&(strstr((oObj+k)->name, (oObj+n)->name)==0)&&(strstr((oObj+l)->name, (oObj+n)->name)==0)&&(strstr((oObj+i)->name, (oObj+m)->name)==0)&&(strstr((oObj+j)->name, (oObj+m)->name)==0)&&(strstr((oObj+k)->name, (oObj+m)->name)==0)&&(strstr((oObj+l)->name, (oObj+m)->name)==0)&&(strstr((oObj+n)->name, (oObj+m)->name)==0)) {
							sz=strlen((oObj+i)->name);
							combi[cont*param_nb]=malloc((sz+1)*sizeof(char));
							strcpy(combi[cont*param_nb], (oObj+i)->name);
							strcpy(combi[cont*param_nb]+sz, "\0");

							sz=strlen((oObj+j)->name);
							combi[cont*param_nb+1]=malloc((sz+1)*sizeof(char));
							strcpy(combi[cont*param_nb+1], (oObj+j)->name);
							strcpy(combi[cont*param_nb+1]+sz, "\0");

							sz=strlen((oObj+k)->name);
							combi[cont*param_nb+2]=malloc((sz+1)*sizeof(char));
							strcpy(combi[cont*param_nb+2], (oObj+k)->name);
							strcpy(combi[cont*param_nb+2]+sz, "\0");

							sz=strlen((oObj+l)->name);
							combi[cont*param_nb+3]=malloc((sz+1)*sizeof(char));
							strcpy(combi[cont*param_nb+3], (oObj+l)->name);
							strcpy(combi[cont*param_nb+3]+sz, "\0");

							sz=strlen((oObj+n)->name);
							combi[cont*param_nb+4]=malloc((sz+1)*sizeof(char));
							strcpy(combi[cont*param_nb+4], (oObj+n)->name);
							strcpy(combi[cont*param_nb+4]+sz, "\0");

							sz=strlen((oObj+m)->name);
							combi[cont*param_nb+5]=malloc((sz+1)*sizeof(char));
							strcpy(combi[cont*param_nb+5], (oObj+m)->name);
							strcpy(combi[cont*param_nb+5]+sz, "\0");
							cont++;
                          }
                        }
                      }
            else{
              if((strstr((oObj+i)->name, (oObj+j)->name)==0)&&(strstr((oObj+i)->name, (oObj+k)->name)==0)&&(strstr((oObj+j)->name, (oObj+k)->name)==0)&&(strstr((oObj+i)->name, (oObj+l)->name)==0)&&(strstr((oObj+j)->name, (oObj+l)->name)==0)&&(strstr((oObj+k)->name, (oObj+l)->name)==0)&&(strstr((oObj+i)->name, (oObj+n)->name)==0)&&(strstr((oObj+j)->name, (oObj+n)->name)==0)&&(strstr((oObj+k)->name, (oObj+n)->name)==0)&&(strstr((oObj+l)->name, (oObj+n)->name)==0)) {
							sz=strlen((oObj+i)->name);
							combi[cont*param_nb]=malloc((sz+1)*sizeof(char));
							strcpy(combi[cont*param_nb], (oObj+i)->name);
							strcpy(combi[cont*param_nb]+sz, "\0");

							sz=strlen((oObj+j)->name);
							combi[cont*param_nb+1]=malloc((sz+1)*sizeof(char));
							strcpy(combi[cont*param_nb+1], (oObj+j)->name);
							strcpy(combi[cont*param_nb+1]+sz, "\0");

							sz=strlen((oObj+k)->name);
							combi[cont*param_nb+2]=malloc((sz+1)*sizeof(char));
							strcpy(combi[cont*param_nb+2], (oObj+k)->name);
							strcpy(combi[cont*param_nb+2]+sz, "\0");

							sz=strlen((oObj+l)->name);
							combi[cont*param_nb+3]=malloc((sz+1)*sizeof(char));
							strcpy(combi[cont*param_nb+3], (oObj+l)->name);
							strcpy(combi[cont*param_nb+3]+sz, "\0");

							sz=strlen((oObj+n)->name);
							combi[cont*param_nb+4]=malloc((sz+1)*sizeof(char));
							strcpy(combi[cont*param_nb+4], (oObj+n)->name);
							strcpy(combi[cont*param_nb+4]+sz, "\0");
							cont++;
            }
						}
          }
          }
          else{
            if((strstr((oObj+i)->name, (oObj+j)->name)==0)&&(strstr((oObj+i)->name, (oObj+k)->name)==0)&&(strstr((oObj+j)->name, (oObj+k)->name)==0)&&(strstr((oObj+i)->name, (oObj+l)->name)==0)&&(strstr((oObj+j)->name, (oObj+l)->name)==0)&&(strstr((oObj+k)->name, (oObj+l)->name)==0)) {
						sz=strlen((oObj+i)->name);
						combi[cont*param_nb]=malloc((sz+1)*sizeof(char));
						strcpy(combi[cont*param_nb], (oObj+i)->name);
						strcpy(combi[cont*param_nb]+sz, "\0");

						sz=strlen((oObj+j)->name);
						combi[cont*param_nb+1]=malloc((sz+1)*sizeof(char));
						strcpy(combi[cont*param_nb+1], (oObj+j)->name);
						strcpy(combi[cont*param_nb+1]+sz, "\0");

						sz=strlen((oObj+k)->name);
						combi[cont*param_nb+2]=malloc((sz+1)*sizeof(char));
						strcpy(combi[cont*param_nb+2], (oObj+k)->name);
						strcpy(combi[cont*param_nb+2]+sz, "\0");

						sz=strlen((oObj+l)->name);
						combi[cont*param_nb+3]=malloc((sz+1)*sizeof(char));
						strcpy(combi[cont*param_nb+3], (oObj+l)->name);
						strcpy(combi[cont*param_nb+3]+sz, "\0");
						cont++;
          }
					}
                  }
                }
        else{
          if((strstr((oObj+i)->name, (oObj+j)->name)==0)&&(strstr((oObj+i)->name, (oObj+k)->name)==0)&&(strstr((oObj+j)->name, (oObj+k)->name)==0)) {
					sz=strlen((oObj+i)->name);
					combi[cont*param_nb]=malloc((sz+1)*sizeof(char));
					strcpy(combi[cont*param_nb], (oObj+i)->name);
					strcpy(combi[cont*param_nb]+sz, "\0");

					sz=strlen((oObj+j)->name);
					combi[cont*param_nb+1]=malloc((sz+1)*sizeof(char));
					strcpy(combi[cont*param_nb+1], (oObj+j)->name);
					strcpy(combi[cont*param_nb+1]+sz, "\0");

					sz=strlen((oObj+k)->name);
					combi[cont*param_nb+2]=malloc((sz+1)*sizeof(char));
					strcpy(combi[cont*param_nb+2], (oObj+k)->name);
					strcpy(combi[cont*param_nb+2]+sz, "\0");
					cont++;
				}
      }
      }
      }
      else{
        if(strstr((oObj+i)->name, (oObj+j)->name)==0) {
				   sz=strlen((oObj+i)->name);
				   combi[cont*param_nb]=malloc((sz+1)*sizeof(char));
           strcpy(combi[cont*param_nb], (oObj+i)->name);
				   strcpy(combi[cont*param_nb]+sz, "\0");

				   sz=strlen((oObj+j)->name);
				   combi[cont*param_nb+1]=malloc((sz+1)*sizeof(char));
				   strcpy(combi[cont*param_nb+1], (oObj+j)->name);
				   strcpy(combi[cont*param_nb+1]+sz, "\0");
				   cont++;
         }
			}
    }
    }
    else{
			sz=strlen((oObj+i)->name);
			combi[cont]=malloc((sz+1)*sizeof(char));
			strcpy(combi[cont], (oObj+i)->name);
			strcpy(combi[cont]+sz, "\0");

			cont++;
		}
    }

	  cont1=0;
	  k=0;

      precond = (char**)malloc((20)*sizeof(char*)); //stores the predicates or effects
		printf("\n");
		while (strstr(search, ":effect")==0) {

			 //any word in the line
       if (strstr(search,"(not")!=0) {
         neg_indicator = 1;

       }
			if ((strstr(search, "(and")==0)&&(strstr(search, "(or")==0)&&(strstr(search,"(not")==0)&&(strstr(search,")")==0)) {
				sz = strlen(search);
				if(strstr(search, "(")!=0){
				  for(l=0;l<sz;l++){
					    search[l]=search[l+1];

				  }
          if (neg_indicator) {
            neg_num++;

          }
          else {
            neg_indicator = 0;
            cond_indicator = 0;
            pos_num++;
          }
          p_num++;
				  sz--;
				}
        if(strstr(search, "(")!=0){
          for(l=0;l<sz;l++){
            search[l]=search[l+1];

          }
          sz--;
        }

				precond[k] = malloc((sz+1)*sizeof(char));
				strcpy(precond[k], search);
				strcpy(precond[k]+sz, "\0");
				k++;
			  }

			else if ((strstr(search, ")")!=0) && (strlen(search)>1)){ //when last word arrives
				sz = strlen(search);
				search[sz-1]="\0";
				sz--;
        if(strstr(search, "(")!=0){
          for(l=0;l<sz;l++){
            search[l]=search[l+1];
          }
          sz--;
        }
        if(strstr(search, "(")!=0){
          for(l=0;l<sz;l++){
            search[l]=search[l+1];
          }
          sz--;
        }
        if(strstr(search,")")!=0){
          search[sz-1]="\0";
          sz--;
        }
        if(strstr(search,")")!=0){
          search[sz-1]="\0";
          sz--;
        }

				precond[k] = malloc((sz+1)*sizeof(char));
				strcpy(precond[k], search);
				strcpy(precond[k]+sz, "\0");
				k++;
        int r=0;
        for (r=0; r<cont; r++) {
          aAction[act_num+r].name = malloc((strlen(action_name)+1)*sizeof(char));
          strcpy(aAction[act_num+r].name, action_name);
          if (neg_indicator) {
            aAction[act_num+r].neg_precond[neg_num-1].atom_name= malloc(sizeof(char)*(strlen(precond[0])+1));
            strcpy(aAction[act_num+r].neg_precond[neg_num-1].atom_name,precond[0]);
            aAction[act_num+r].neg_precond[neg_num-1].arg_num=k-1;
            aAction[act_num+r].neg_precond_num = neg_num;

				    for(j=1;j<k;j++){
					     for(i=0;i<param_nb;i++){
                 if(strcmp(precond[j],(question+i)->name)==0){
                   aAction[act_num+r].neg_precond[neg_num-1].argument[j-1] = malloc(strlen((1+combi[r*param_nb+i]))*sizeof(char));
                   strcpy(aAction[act_num+r].neg_precond[neg_num-1].argument[j-1], combi[r*param_nb+i]);
                 }
               }
					  }
				  }
          else {

            aAction[act_num+r].precond[pos_num-1].atom_name= malloc(sizeof(char)*(strlen(precond[0])+1));
            strcpy(aAction[act_num+r].precond[pos_num-1].atom_name, precond[0]);
            aAction[act_num+r].precond[pos_num-1].arg_num=k-1;
            aAction[act_num+r].precond_num = pos_num;
				    for(j=1;j<k;j++){
					     for(i=0;i<param_nb;i++){
                 if(strcmp(precond[j],(question+i)->name)==0){
                   aAction[act_num+r].precond[pos_num-1].argument[j-1] = malloc(strlen((1+combi[r*param_nb+i]))*sizeof(char));
                   strcpy(aAction[act_num+r].precond[pos_num-1].argument[j-1], combi[r*param_nb+i]);
						     }
               }
					  }
          }

        }
        k=0;
        m=0;

			}

			fscanf(dom_ptr, "%s", search);
			strncpy(stop_finder, search, 3);
			stop_finder[3] = '\0';

		}
		fscanf(dom_ptr, "%s", search);
		k=0;
    cond_indicator=0;
    neg_indicator = 0;
		j=0;
    cond_num=0;
    p_num = 0;
    pos_num = 0;
    neg_num = 0;
    while (strlen(search)>1) {
      if(strstr(search, "(when")!=0) {
        cond_indicator = 1;
      }
      if (strstr(search,"(not")!=0) {
        neg_indicator = 1;
      }
      if(strcmp(search,"(increase")==0){

            fscanf(dom_ptr, "%s", search);
            fscanf(dom_ptr, "%s", search);
            cost = atoi(search);
            for (r=0; r<cont; r++) {
              aAction[act_num+r].cost = cost;
            }
            break;
          }
        else if ((strstr(search, "(and")==0)&&(strstr(search, "(or")==0)&&(strstr(search,"(not")==0)&&(strstr(search, ")")==0)&&(strstr(search,"(when")==0)) {
          sz = strlen(search);
          if(strstr(search, "(")!=0){
            for(l=0;l<sz;l++){
              search[l]=search[l+1];
            }
            if (neg_indicator&&!cond_indicator) {
              neg_num++;
            }
            if (cond_indicator) {
              cond_num++;
            }
            else if(neg_indicator==0){
              pos_num++;
            }
            p_num++;
            sz--;
          }
          if(strstr(search,")")!=0){
            search[sz-1]="\0";
            sz--;
          }
          precond[k] = malloc((sz+1)*sizeof(char));
          strcpy(precond[k], search);
          strcpy(precond[k]+sz, "\0");
          k++;
        }
        else if ((strstr(search,")")!=0)&&(strlen(search)>1)) {
          sz = strlen(search);
          search[sz-1]="\0";
          sz--;

          if(strstr(search,")")!=0){
            search[sz-1]="\0";
            sz--;
          }
          if(strstr(search,")")!=0){
            search[sz-1]="\0";
            sz--;
          }
          if(strstr(search, "(")!=0){
            for(l=0;l<sz;l++){
              search[l]=search[l+1];

            }
            sz--;
          }
          precond[k] = malloc((sz+1)*sizeof(char));
          strcpy(precond[k], search);
          strcpy(precond[k]+sz, "\0");
          k++;
          for (r=0; r<cont; r++) {
            if (neg_indicator&&!cond_indicator) {
              aAction[act_num+r].neg_effect[neg_num-1].atom_name= malloc(sizeof(char)*(strlen(precond[0])+1));
              strcpy(aAction[act_num+r].neg_effect[neg_num-1].atom_name, precond[0]);
              aAction[act_num+r].neg_effect[neg_num-1].arg_num=k-1;
              aAction[act_num+r].neg_effect_num = neg_num;
              for(j=1;j<k;j++){
                for(i=0;i<param_nb;i++){
				           if(strcmp(precond[j],(question+i)->name)==0){
                     aAction[act_num+r].neg_effect[neg_num-1].argument[j-1] = malloc(strlen((1+combi[r*param_nb+i]))*sizeof(char));
                     strcpy(aAction[act_num+r].neg_effect[neg_num-1].argument[j-1], combi[r*param_nb+i]);
				           }
                }
              }
            }
            else if (cond_indicator) {
              if (neg_indicator) {
                aAction[act_num+r].neg_cond[cond_num-1].atom_name= malloc(sizeof(char)*(strlen(precond[0])));

                strcpy(aAction[act_num+r].neg_cond[cond_num-1].atom_name, precond[0]);
                aAction[act_num+r].neg_cond[cond_num-1].arg_num=k-1;
                aAction[act_num+r].neg_cond[cond_num-1].argument = malloc((k)*sizeof(char*));
                aAction[act_num+r].neg_cond_num = cond_num;

                for(j=1;j<k;j++){
                  for(i=0;i<param_nb;i++){
				             if(strcmp(precond[j],(question+i)->name)==0){
                        aAction[act_num+r].neg_cond[cond_num-1].argument[j-1] = malloc(strlen((1+combi[r*param_nb+i]))*sizeof(char));
                        strcpy(aAction[act_num+r].neg_cond[cond_num-1].argument[j-1], combi[r*param_nb+i]);
				             }
                   }
                 }
                 aAction[act_num+r].cond_effect[cond_num-1].atom_name= malloc(sizeof(char)*(strlen(precond[0])));
                 strcpy(aAction[act_num+r].cond_effect[cond_num-1].atom_name, precond[0]);
                 aAction[act_num+r].cond_effect[cond_num-1].arg_num=k-1;
                 aAction[act_num+r].cond_effect[cond_num-1].argument = malloc((k)*sizeof(char*));
                 aAction[act_num+r].neg_cond_num = cond_num;

                 for(j=1;j<k;j++){
                   for(i=0;i<param_nb;i++){
 				             if(strcmp(precond[j],(question+i)->name)==0){
                         aAction[act_num+r].cond_effect[cond_num-1].argument[j-1] = malloc(strlen((1+combi[r*param_nb+i]))*sizeof(char));
                         strcpy(aAction[act_num+r].cond_effect[cond_num-1].argument[j-1], combi[r*param_nb+i]);
 				             }
                    }
                  }
                  if (r==cont-1) {
                    cond_indicator = 0;
                    fscanf(dom_ptr, "%s", search);
                    fscanf(dom_ptr, "%s", search);
                  }
               }
               else {
                 aAction[act_num+r].cond[cond_num-1].atom_name= malloc(sizeof(char)*(strlen(precond[0])+1));
                 strcpy(aAction[act_num+r].cond[cond_num-1].atom_name, precond[0]);
                 aAction[act_num+r].cond[cond_num-1].arg_num=k-1;
                 aAction[act_num+r].cond_num = cond_num;
                 for(j=1;j<k;j++){
                   for(i=0;i<param_nb;i++){
                      if(strcmp(precond[j],(question+i)->name)==0){
                         aAction[act_num+r].cond[cond_num-1].argument[j-1] = malloc(strlen((1+combi[r*param_nb+i]))*sizeof(char));
                         strcpy(aAction[act_num+r].cond[cond_num-1].argument[j-1], combi[r*param_nb+i]);
                      }
                    }
                  }
                  aAction[act_num+r].neg_cond_effect[cond_num-1].atom_name= malloc(sizeof(char)*(strlen(precond[0])));
                  strcpy(aAction[act_num+r].neg_cond_effect[cond_num-1].atom_name, precond[0]);
                  aAction[act_num+r].neg_cond_effect[cond_num-1].arg_num=k-1;
                  aAction[act_num+r].neg_cond_effect[cond_num-1].argument = malloc((k)*sizeof(char*));
                  aAction[act_num+r].cond_num = cond_num;

                  for(j=1;j<k;j++){
                    for(i=0;i<param_nb;i++){
  				             if(strcmp(precond[j],(question+i)->name)==0){
                          aAction[act_num+r].neg_cond_effect[cond_num-1].argument[j-1] = malloc(strlen((1+combi[r*param_nb+i]))*sizeof(char));
                          strcpy(aAction[act_num+r].neg_cond_effect[cond_num-1].argument[j-1], combi[r*param_nb+i]);
  				             }
                     }
                   }
                   if (r==cont-1) {
                     cond_indicator = 0;
                     fscanf(dom_ptr, "%s", search);
                     fscanf(dom_ptr, "%s", search);
                   }
                }
             }
             else {
              aAction[act_num+r].effect[pos_num-1].atom_name= malloc(sizeof(char)*(strlen(precond[0])+1));
              strcpy(aAction[act_num+r].effect[pos_num-1].atom_name,  precond[0]);
              aAction[act_num+r].effect[pos_num-1].arg_num=k-1;
              aAction[act_num+r].effect_num = pos_num;

              for(j=1;j<k;j++){
                for(i=0;i<param_nb;i++){
				           if(strcmp(precond[j],(question+i)->name)==0){
                     aAction[act_num+r].effect[pos_num-1].argument[j-1] = malloc(strlen((1+combi[r*param_nb+i]))*sizeof(char));
                     strcpy(aAction[act_num+r].effect[pos_num-1].argument[j-1], combi[r*param_nb+i]);

				           }
                }
              }
            }
          }
          k=0;
        }
        fscanf(dom_ptr, "%s", search);
        strncpy(stop_finder, search, 3);
        stop_finder[3] = '\0';

	  }
    cond_indicator=0;
    neg_indicator=0;
    pos_num = 0;
    neg_num = 0;
     act_num+=cont;


      param_nb=0;
      j=0;
      k=0;
      for (int j=0; j<3; j++) {
        stop_finder[j] = '\0';
      }
    }
  }

  for (i=0; i<act_num; i++) {
    printf("%s\n", aAction[i].name);

    for (j=0;j<aAction[i].precond_num; j++) {
        printf("p: %s ", aAction[i].precond[j].atom_name);
        printf("(");
      for (k=0; k<aAction[i].precond[j].arg_num; k++) {
          printf("%s ", aAction[i].precond[j].argument[k]);
      }
      printf(")\n");
    }
    for (j=0;j<aAction[i].neg_precond_num; j++) {
        printf("np: (not %s ", aAction[i].neg_precond[j].atom_name);
        printf("(");
      for (k=0; k<aAction[i].neg_precond[j].arg_num; k++) {
          printf("%s ", aAction[i].neg_precond[j].argument[k]);
      }
      printf(")\n");
    }
    for (j=0;j<aAction[i].effect_num; j++) {
        printf("e: %s ", aAction[i].effect[j].atom_name);
        printf("(");
      for (k=0; k<aAction[i].effect[j].arg_num; k++) {
          printf("%s ", aAction[i].effect[j].argument[k]);
      }
      printf(")\n");
    }
    for (j=0;j<aAction[i].neg_effect_num; j++) {
        printf("ne:(not %s ", aAction[i].neg_effect[j].atom_name);
        printf("(");
      for (k=0; k<aAction[i].neg_effect[j].arg_num; k++) {
          printf("%s ", aAction[i].neg_effect[j].argument[k]);
      }
      printf(")\n");
    }
    for (j=0;j<aAction[i].neg_cond_num; j++) {
        printf("when (not %s ", aAction[i].neg_cond[j].atom_name);
        printf("(");
      for (k=0; k<aAction[i].neg_cond[j].arg_num; k++) {
          printf("%s ", aAction[i].neg_cond[j].argument[k]);
      }
      printf(") ");
    }
    for (j=0;j<aAction[i].neg_cond_num; j++) {
        printf(" (%s ", aAction[i].cond_effect[j].atom_name);
        printf("(");
      for (k=0; k<aAction[i].cond_effect[j].arg_num; k++) {
          printf("%s ", aAction[i].cond_effect[j].argument[k]);
      }
      printf(")\n");
    }
    for (j=0;j<aAction[i].cond_num; j++) {
        printf("cond effect: %s ", aAction[i].cond[j].atom_name);
        printf("(");
      for (k=0; k<aAction[i].cond[j].arg_num; k++) {
          printf("%s ", aAction[i].cond[j].argument[k]);
      }
      printf(")\n");
    }
    for (j=0;j<aAction[i].cond_num; j++) {
        printf(" (%s ", aAction[i].cond_effect[j].atom_name);
        printf("(");
      for (k=0; k<aAction[i].cond_effect[j].arg_num; k++) {
          printf("%s ", aAction[i].cond_effect[j].argument[k]);
      }
      printf(")\n");
    }
    printf("cost: %d\n", aAction[i].cost);
    printf("\n");
  }
	/////////////////////////////////////////////////////////////////////////////
	//Actions Relaxation
	///////////////////////////////////////////////
	relaxed_actions = malloc(act_num*sizeof(Action));
	relaxation(relaxed_actions, aAction, act_num);
	printf("Relaxed Actions\n\n");
	for (i=0; i<act_num; i++) {
		printf("%s\n", relaxed_actions[i].name);
		for (j=0;j<relaxed_actions[i].precond_num; j++) {
			printf("p: %s ", relaxed_actions[i].precond[j].atom_name);
			printf("(");
			for (k=0; k<relaxed_actions[i].precond[j].arg_num; k++) {
				printf("%s ", relaxed_actions[i].precond[j].argument[k]);
			}
			printf(")\n");
		}
		for (j=0;j<relaxed_actions[i].neg_precond_num; j++) {
			printf("np: (not %s ", relaxed_actions[i].neg_precond[j].atom_name);
			printf("(");
			for (k=0; k<relaxed_actions[i].neg_precond[j].arg_num; k++) {
				printf("%s ", relaxed_actions[i].neg_precond[j].argument[k]);
			}
			printf(")\n");
		}
		for (j=0;j<relaxed_actions[i].effect_num; j++) {
			printf("e: %s ", relaxed_actions[i].effect[j].atom_name);
			printf("(");
			for (k=0; k<relaxed_actions[i].effect[j].arg_num; k++) {
				printf("%s ", relaxed_actions[i].effect[j].argument[k]);
			}
			printf(")\n");
		}
		for (j=0;j<relaxed_actions[i].neg_effect_num; j++) {
			printf("ne:(not %s ", relaxed_actions[i].neg_effect[j].atom_name);
			printf("(");
			for (k=0; k<relaxed_actions[i].neg_effect[j].arg_num; k++) {
				printf("%s ", relaxed_actions[i].neg_effect[j].argument[k]);
			}
			printf(")\n");
		}
		printf("cost: %d\n", relaxed_actions[i].cost);
		printf("\n");
	}
	int sz_states_list=10000;
	states_list=malloc(sz_states_list*sizeof(State));
	//////////////////////////
	//Initial state storage
	//////////////////////////
	state = (Atom*)malloc((sizeof(Atom))*(1000));
	fseek(p_ptr, 0, SEEK_SET);
	for (int j=0; j<2; j++) {
		stop_finder[j] = '\0';
	}
	int numb = 0;
	int state_anum=0;
	while (!feof(p_ptr)) {
		fscanf(p_ptr, "%s", init_finder);
		if (strstr(init_finder, "init")!=0) {
			fscanf(p_ptr, "%s", search);
			while (strstr(search, "(:")==0) {
				while (strstr(search, ")")==0) {
					fscanf(p_ptr, "%s", search);
					numb++;
				}
				(state+state_anum)->argument = (char**)malloc((numb+1)*sizeof(char*));
				numb=0;
				fscanf(p_ptr, "%s", search);
				state_anum++;
			}
			break;
		}
	}
	fseek(p_ptr, 0, SEEK_SET);
	for (int j=0; j<2; j++) {
		stop_finder[j] = '\0';
	}
	numb = 0;
	state_anum=0;
	while (!feof(p_ptr)) {
		fscanf(p_ptr, "%s", init_finder);
		if (strstr(init_finder, "init")!=0) {
			fscanf(p_ptr, "%s", search);
			while (strstr(search, "(:")==0) {
				if (numb==0) {
					sz=strlen(search);
					(state+state_anum)->atom_name = malloc((sz+1)*(sizeof(char)));
					strcpy((state+state_anum)->atom_name, search);
					if(strstr((state+state_anum)->atom_name, "(")!=0){
						for(l=0;l<sz;l++){
							(state+state_anum)->atom_name[l]=(state+state_anum)->atom_name[l+1];
						}
						sz--;
					}
					if(strstr((state+state_anum)->atom_name,")")!=0){
						(state+state_anum)->atom_name[sz-1]="\0";
						sz--;
					}
					if(strstr((state+state_anum)->atom_name,")")!=0){
						(state+state_anum)->atom_name[sz-1]="\0";
						sz--;
					}
				}
				while (strstr(search, ")")==0) {
					fscanf(p_ptr, "%s", search);
					sz = strlen(search);
					(state+state_anum)->argument[numb] = malloc((sz+1)*sizeof(char));
					strcpy((state+state_anum)->argument[numb], search);
					if(strstr((state+state_anum)->argument[numb],")")!=0){
						(state+state_anum)->argument[numb][sz-1]='\0';
						sz--;
					}
					if(strstr((state+state_anum)->argument[numb],")")!=0){
						(state+state_anum)->argument[numb][sz-1]='\0';
						sz--;
					}
					if(strstr((state+state_anum)->argument[numb],")")!=0){
						(state+state_anum)->argument[numb][sz-1]='\0';
						sz--;
					}
					numb++;
				}
				(state+state_anum)->arg_num = numb;
				numb=0;
				fscanf(p_ptr, "%s", search);
				state_anum++;
			}
			break;
		}
	}
	//initialize initial state
	(states_list+0)->state_num=0;
	(states_list+0)->anum=state_anum;
	(states_list+0)->curr_state=malloc((states_list->anum)*sizeof(Atom));
	for (i=0; i<states_list->anum; i++) {
		(states_list+0)->curr_state[i].atom_name = malloc(strlen((state+i)->atom_name)*sizeof(char));
		strcpy((states_list+0)->curr_state[i].atom_name, (state+i)->atom_name);
		(states_list+0)->curr_state[i].arg_num = (state+i)->arg_num;
		(states_list+0)->curr_state[i].argument = malloc((states_list+0)->curr_state[i].arg_num*sizeof(char*));
		for (j=0; j<(states_list+0)->curr_state[i].arg_num; j++) {
			(states_list+0)->curr_state[i].argument[j] = malloc(strlen((state+i)->argument[j])*sizeof(char));
			strcpy((states_list+0)->curr_state[i].argument[j], (state+i)->argument[j]);
		}
	}
	(states_list+0)->curr_state=state;
	(states_list+0)->num_possible_actions=0;
	(states_list+0)->possible_actions=malloc(act_num*sizeof(Action));
	(states_list+0)->next_states=(State*)malloc(act_num*sizeof(State));
	(states_list+0)->pred=NULL;
	(states_list+0)->f=0;
	(states_list+0)->h=0;
	//////////////////////////////////////////////////////////////////////////////
	//Goal state storage
	////////////////////////////////////////////////////////////////////////////////
	fseek(p_ptr, 0, SEEK_SET);
	for (int j=0; j<2; j++) {
		stop_finder[j] = '\0';
	}
	numb = 0;
	state_anum=0;
	goal = (Atom*)malloc(sizeof(Atom)*100);
	while (!feof(p_ptr)) {
		fscanf(p_ptr, "%s", goal_finder);
		if (strstr(goal_finder, "goal")!=0) {
			fscanf(p_ptr, "%s", search);
			while ((strstr(search, "(:")==0)&&(strlen(search)>1)) {
				if (strstr(search, "and")!=0) {
					fscanf(p_ptr, "%s", search);
				}
				while (strstr(search, ")")==0) {
					fscanf(p_ptr, "%s", search);
					numb++;
				}
				(goal+state_anum)->argument = (char**)malloc((numb)*sizeof(char*));
				numb=0;
				fscanf(p_ptr, "%s", search);
				state_anum++;
				if((strstr(search, "))")!=0)) {
					break;
				}
			}
			break;
		}
	}
	fseek(p_ptr, 0, SEEK_SET);
	for (int j=0; j<2; j++) {
		stop_finder[j] = '\0';
	}
	numb = 0;
	state_anum=0;
	while (!feof(p_ptr)) {
		fscanf(p_ptr, "%s", goal_finder);
		if (strstr(goal_finder, "goal")!=0) {
			fscanf(p_ptr, "%s", search);
			while ((strstr(search, "(:")==0)&&(strlen(search)>1)) {
				if (strstr(search, "and")!=0) {
					fscanf(p_ptr, "%s", search);
				}
				if (numb==0) {
					sz=strlen(search);
					(goal+state_anum)->atom_name = malloc((sz+1)*(sizeof(char)));
					strcpy((goal+state_anum)->atom_name, search);
					if(strstr((goal+state_anum)->atom_name, "(")!=0){
						for(l=0;l<sz;l++){
							(goal+state_anum)->atom_name[l]=(goal+state_anum)->atom_name[l+1];
						}
						sz--;
					}
					if(strstr((goal+state_anum)->atom_name,")")!=0){
						(goal+state_anum)->atom_name[sz-1]='\0';
						sz--;
					}
				}
				while (strstr(search, ")")==0) {
					fscanf(p_ptr, "%s", search);
					sz = strlen(search);
					(goal+state_anum)->argument[numb] = malloc((sz+1)*sizeof(char));
					strcpy((goal+state_anum)->argument[numb], search);
					if(strstr((goal+state_anum)->argument[numb],")")!=0){
						(goal+state_anum)->argument[numb][sz-1]='\0';
						sz--;
					}
					if(strstr((goal+state_anum)->argument[numb],")")!=0){
						(goal+state_anum)->argument[numb][sz-1]='\0';
						sz--;
					}
					if(strstr((goal+state_anum)->argument[numb],")")!=0){
						(goal+state_anum)->argument[numb][sz-1]='\0';
						sz--;
					}
					if(strstr((goal+state_anum)->argument[numb],")")!=0){
						(goal+state_anum)->argument[numb][sz-1]='\0';
						sz--;
					}
					numb++;
				}
				(goal+state_anum)->arg_num = numb;
				numb=0;
				fscanf(p_ptr, "%s", search);
				state_anum++;
				if((strstr(search, "))")!=0)) {
					break;
				}
			}
			break;
		}
	}
	//initialize goal state
	(states_list+1)->state_num=1;
	(states_list+1)->anum=state_anum;
	(states_list+1)->curr_state=malloc(((states_list+1)->anum)*sizeof(Atom));
	(states_list+1)->curr_state=goal;
	(states_list+1)->num_possible_actions=0;
	(states_list+1)->possible_actions=malloc(act_num*sizeof(Action));
	(states_list+1)->next_states=malloc(act_num*sizeof(State));
	(states_list+1)->pred=NULL;
	(states_list+1)->f=10000;
	(states_list+1)->h=0;
	///////////////////////////////////////////////////////////////////////////////
	//A STAR
	//////////////////////////////////////////////////////////////////////////////
	int choice_heuristics;
	printf("Choose the heuristics:\n 1 for Delete relaxation\n 2 for Critical path h^2\n");
	scanf("%d",&choice_heuristics);
	int when_bug_change=10000, not_copy;
	int nexts[when_bug_change];
	int f_in_nexts[when_bug_change];
	int pi[when_bug_change];
	int heuristics[50];
	for (i=0; i<50; i++) {
		heuristics[i]=0;
	}
	for(i=0;i<when_bug_change;i++){
		nexts[i]=0;
		f_in_nexts[i]=10000;
	}
	///////////////////////////////////////////////////////////////////////////////
	//Delete relaxation heuristic
	//////////////////////////////////////////////////////////////////////////////
	if(choice_heuristics==1){
		int sz_nexts=0;
		flag=1;
		j=0;
		index=2;
		while(flag==1){
			if(states_list[j].state_num==nexts[0]){
				nexts[0]=0; //erase the current state in nexts
				f_in_nexts[0]=10000;
				if(sz_nexts!=0){
					for(int p=0;p<=index;p++){
						nexts[p]=nexts[p+1];
						f_in_nexts[p]=f_in_nexts[p+1];
					}
				}
				if (j==0) {
					search_possible_actions(j,states_list,aAction,act_num);
					create_next_states(j,states_list,aAction,act_num);
					index=copy_next_states_if_new(j,states_list, index,act_num);
					for (int k=2; k<index; k++) {
						for (int l=0; l<states_list[1].anum;l++) {
							heuristics[l] = dr_heuristic(states_list[j+k], relaxed_actions, states_list[1].curr_state[l], act_num);
						}
						for (int l=0; l<states_list[1].anum;l++) {
							if (states_list[j+k].h<heuristics[l]) {
								states_list[j+k].h = heuristics[l];
							}
						}
					}
				}
				else {
					search_possible_actions(j,states_list,aAction,act_num);
					create_next_states(j,states_list,aAction,act_num);
					index=copy_next_states_if_new(j,states_list, index,act_num);
					for (int k=1; k<index-j; k++) {
						for (int l=0; l<states_list[1].anum;l++) {
							heuristics[l] = dr_heuristic(states_list[j+k], relaxed_actions, states_list[1].curr_state[l], act_num);
						}
						for (int l=0; l<states_list[1].anum;l++) {
							if (states_list[j+k].h<heuristics[l]) {
								states_list[j+k].h = heuristics[l];
							}
						}
					}
				}
				for(int k=0;k<states_list[j].num_possible_actions;k++){
					for(int l=0;l<index;l++){
						if(states_list[j].next_states[k].state_num==states_list[l].state_num){
							if(states_list[l].f>((states_list[j].f)+(states_list[j].possible_actions[k].cost))){
								states_list[l].f=(states_list[j].f+(states_list[j].possible_actions[k].cost));
								(states_list+l)->pred=&(states_list[j]);
								sz_nexts=0;
								for(int m=0;m<when_bug_change;m++){
									if(f_in_nexts[m]!=10000){
										sz_nexts++;	//compute the size of nexts
									}
								}
								if (sz_nexts==0){
									nexts[0]=states_list[l].state_num;
									f_in_nexts[0]=(states_list[l].f)+(states_list[l].h);
								}
								else if (sz_nexts>0){
									for(int n=0;n<sz_nexts;n++){
										//compare states_list[l].f with f of the states in nexts
										if (((states_list[l].f)+(states_list[l].h))<f_in_nexts[n]) {
											if (states_list[l].state_num==nexts[n]) {
												nexts[n]=states_list[l].state_num;
												f_in_nexts[n]=(states_list[l].f)+(states_list[l].h);
											}
											else {
												for(int p=sz_nexts;p>n-1;p--){
													nexts[p+1]=nexts[p];
													f_in_nexts[p+1]=f_in_nexts[p];
												}
												nexts[n]=states_list[l].state_num;
												f_in_nexts[n]=(states_list[l].f)+(states_list[l].h);
											}
										}
										else if (((states_list[l].f)+(states_list[l].h))>=f_in_nexts[n]&&n==(sz_nexts-1)&&(states_list[l].state_num!=nexts[n])){
											nexts[sz_nexts]=states_list[l].state_num;
											f_in_nexts[sz_nexts]=(states_list[l].f)+(states_list[l].h);
										}
									}
								}
							}
						}
					}
				}
			}
			else{
				if(j<index){
					if (j==0) {
						j++;
					}
					j++;
				}
				else if(j==index){
					j=0;
				}
			}
			flag=0;
			for(i=0;i<when_bug_change;i++){
				if(nexts[i]!=0) {
					flag=1;
				}
			}
			if((is_it_goal(states_list[nexts[0]],states_list[1])==states_list[1].anum)&&(j!=1)){
				flag=0;
				break;
			}
		}
		int goal_states[index];
		for(i=0;i<index;i++){
			goal_states[i]=0;
		}
		for(i=0;i<index;i++){
			if(is_it_goal(states_list[i],states_list[1])>0&&i!=1){
				goal_states[i]=is_it_goal(states_list[i],states_list[1]);
			}
		}
		int nn=0;
		for(i=0;i<index;i++){
			if (goal_states[i] == states_list[1].anum) {
				nn=goal_states[i];
			}
		}
		if(nn!=states_list[1].anum) {
			printf("Goal not found. No plan\n");
			return(0);
		}
		//Make the plan from the predecessors from G
		j=index-1;
		sz_nexts=0; //we will use it to store the size of pi
		for(i=0;i<index;i++){
			pi[i]=10000;
		}
		for(i=0;i<index;i++){
			if(goal_states[i]!=0){
				pi[0]=i;
			}
		}
		while(pi[0]!=0){
			for(i=index-1;i>0;i--){
				if(pi[0]==states_list[i].state_num){
					for(j=0;j<index;j++){
						if(states_list[j].state_num==states_list[i].pred->state_num){
							//compute the size of pi
							sz_nexts=0;
							for(int k=0;k<index;k++){
								if(pi[k]!=10000){
									sz_nexts++;
								}
							}
							//shift right
							for(int p=sz_nexts;p>=0;p--){
								pi[p+1]=pi[p];
							}
							//copy (states_list+i)->pred in pi[0]
							pi[0]=states_list[i].pred->state_num;
						}
					}
				}
			}
		}
		printf("\nplan_dr={ ");
		for(i=0;i<index;i++){
			if(pi[i]!=10000){
				printf("S%d ",pi[i]);
			}
		}
		printf("}\n");
		printf("\nStates in the plan\n");
		for(i=0;i<index;i++){
			if(pi[i]!=10000){
				print_State(states_list[pi[i]]);
			}
		}
	}
	///////////////////////////////////////////
	//Critical path heuristics
	////////////////////////////////////////////
	else if(choice_heuristics==2){
		int sz_nexts=0;
		flag=1;
		j=0;
		index=2;
		int var1=1;
		int heuristics2[10][10];
		for (i=0; i<10; i++) {
			for(k=0;k<10;k++){
				heuristics2[i][k]=0;
			}
		}
		while(flag==1){
			if(states_list[j].state_num==nexts[0]){
				nexts[0]=0; //erase the current state in nexts
				f_in_nexts[0]=10000;
				if(sz_nexts!=0){
					for(int p=0;p<=index;p++){
						nexts[p]=nexts[p+1];
						f_in_nexts[p]=f_in_nexts[p+1];
					}
				}
				search_possible_actions(j,states_list,aAction,act_num);
				create_next_states(j,states_list,aAction,act_num);
				index=copy_next_states_if_new(j,states_list, index,act_num);
				for (int k=0; k<states_list[j].num_possible_actions; k++) {
					if(states_list[1].anum==1){
						states_list[states_list[j].next_states[k].state_num].h=new_cr_heuristic_1goal(states_list[j].next_states[k], relaxed_actions, states_list[1].curr_state[0], act_num);
					}
					else if(states_list[1].anum==2){
						states_list[states_list[j].next_states[k].state_num].h=new_cr_heuristic(states_list[j].next_states[k], relaxed_actions, states_list[1].curr_state[0],states_list[1].curr_state[1], act_num);
					}
					else if (states_list[1].anum>2){
						for (int l=0; l<states_list[1].anum;l++) {
							for(int m=0;m<states_list[1].anum;m++){
								if(l!=m&&l<m){
									heuristics2[l][m] = new_cr_heuristic(states_list[j].next_states[k], relaxed_actions, states_list[1].curr_state[l],states_list[1].curr_state[m], act_num);
								}
							}
						}
						for (int l=0; l<states_list[1].anum;l++) {
							for(int m=0;m<states_list[1].anum;m++){
								if (states_list[states_list[j].next_states[k].state_num].h<heuristics2[l][m]) {
									states_list[states_list[j].next_states[k].state_num].h= heuristics2[l][m];
								}
							}
						}

					}
				}
				for(int k=0;k<states_list[j].num_possible_actions;k++){
					for(int l=0;l<index;l++){
						if(states_list[j].next_states[k].state_num==states_list[l].state_num){
							if(states_list[l].f>((states_list[j].f)+(states_list[j].possible_actions[k].cost))){

								states_list[l].f=(states_list[j].f+(states_list[j].possible_actions[k].cost));
								(states_list+l)->pred=&(states_list[j]);
								sz_nexts=0;
								for(int m=0;m<when_bug_change;m++){
									if(f_in_nexts[m]!=10000){
										sz_nexts++;	//compute the size of nexts
									}
								}
								if (sz_nexts==0){
									nexts[0]=states_list[l].state_num;
									f_in_nexts[0]=(states_list[l].f)+(states_list[l].h);
								}
								else if (sz_nexts>0){
									for(int n=0;n<sz_nexts;n++){
										//compare states_list[l].f with f of the states in nexts
										if (((states_list[l].f)+(states_list[l].h))<f_in_nexts[n]) {
											if (states_list[l].state_num==nexts[n]) {
												nexts[n]=states_list[l].state_num;
												f_in_nexts[n]=(states_list[l].f)+(states_list[l].h);
											}
											else {
												for(int p=sz_nexts;p>n-1;p--){
													nexts[p+1]=nexts[p];
													f_in_nexts[p+1]=f_in_nexts[p];
												}
												nexts[n]=states_list[l].state_num;
												f_in_nexts[n]=(states_list[l].f)+(states_list[l].h);
											}
										}
										else if (((states_list[l].f)+(states_list[l].h))>=f_in_nexts[n]&&n==(sz_nexts-1)&&(states_list[l].state_num!=nexts[n])){
											nexts[sz_nexts]=states_list[l].state_num;
											f_in_nexts[sz_nexts]=(states_list[l].f)+(states_list[l].h);
										}
									}
								}
							}
						}
					}
				}
			}
			else{
				if(j<index){
					if (j==0) {
						j++;
					}
					j++;
				}
				else if(j==index){
					j=0;
				}
			}
			flag=0;
			for(i=0;i<when_bug_change;i++){
				if(nexts[i]!=0) {
					flag=1;
				}
			}
			if(is_it_goal(states_list[nexts[0]],states_list[1])==states_list[1].anum&&j!=1){
				flag=0;
				break;
			}
		}
		int goal_states[index];
		for(i=0;i<index;i++){
			goal_states[i]=0;
		}
		for(i=0;i<index;i++){
			if(is_it_goal(states_list[i],states_list[1])>0&&i!=1){
				goal_states[i]=is_it_goal(states_list[i],states_list[1]);
			}
		}
		int nn=0;
		for(i=0;i<index;i++){
			if (goal_states[i] == states_list[1].anum) {
				nn=goal_states[i];
			}
		}
		printf("\n");
		if(nn!=states_list[1].anum) {
			printf("Goal not found. No plan\n");
			return(0);
		}
		//Make the plan from the predecessors from G
		j=index-1;
		sz_nexts=0; //we will use it to store the size of pi
		for(i=0;i<index;i++){
			pi[i]=10000;
		}
		for(i=0;i<index;i++){
			if(goal_states[i]!=0){
				pi[0]=i;
			}
		}
		while(pi[0]!=0){
			for(i=index-1;i>0;i--){
				if(pi[0]==states_list[i].state_num){
					for(j=0;j<index;j++){
						if(states_list[j].state_num==states_list[i].pred->state_num){
							//compute the size of pi
							sz_nexts=0;
							for(int k=0;k<index;k++){
								if(pi[k]!=10000){
									sz_nexts++;
								}
							}
							//shift right
							for(int p=sz_nexts;p>=0;p--){
								pi[p+1]=pi[p];
							}
							//copy (states_list+i)->pred in pi[0]
							pi[0]=states_list[i].pred->state_num;
						}
					}
				}
			}
		}
		printf("plan_cr={ ");
			for(i=0;i<index;i++){
				if(pi[i]!=10000){
					printf("S%d ",pi[i]);
				}
			}
			printf("}\n");
			printf("\nStates in the plan\n");
			for(i=0;i<index;i++){
				if(pi[i]!=10000){
					print_State(states_list[pi[i]]);
				}
			}
		}
		else{
			printf("\nWrong number for heuristics\n");
		}
		free(question);
		free(aAction);
		free(combi);
		free(aname);
		free (aAtom);
		free(tType);
		free(oObj);
		fclose(dom_ptr);
		fclose(p_ptr);
		return (0);
	}
