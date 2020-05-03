/**
 * @file   paraminer_local_cgraphs.cpp
 * @author Benjamin Negrevergne <benjamin@neb.dyn.cs.kuleuven.be>
 * @date   Tue Oct 19 18:44:38 2010
 *
 * @brief ParaMiner instance for mining closed frequent gradual itemsets (gri).
 *
 * /!\ This is the gradual definition as it is defined in
 * GLCM. (Handle no variations as positive variations.)  For a more
 * advanced definition of graduals, check
 * paraminer_local_graduals_gen.cpp
 *
 */
#include <cstdlib>
#include <algorithm>
#include <vector>
#include <map>
#include <iostream>
#include <sstream>
#include <fstream>
#include <set>
#include <stdint.h>
#include <cmath>
#include <limits>
#include <chrono>
#include <unistd.h>

#define TRACK_TIDS

#include "paraminer_local.hpp"

#include "pattern.hpp"
#include "database.hpp"
#include "paraminer.hpp"
#include "utils.hpp"
#include "bool_matrix.hpp"

//x//#include "BinaryMatrix.h"


//#define DETECT_NULL_VARIATION 1


using std::cout;
using std::cerr;
using std::endl;
using namespace std;
//x//using namespace nsPattern;

int ELEMENT_RANGE_END;


extern int threshold;

/* Hack to efficiently compute the original pairs of tids */
typedef union{
  uint16_t i16s[2];
  uint32_t i32;
}two_short_t;
#define first_ i16s[0]
#define second_ i16s[1]

typedef two_short_t trans_t;	/**< Virtual transaction descriptor
 type (virtual transactions are created for each pair of original
 transaction. This types holds the tids of the original transactions. */

typedef vector<trans_t> id_trans_t;

typedef std::map<trans_t, id_trans_t> trans_id_t;


int nb_attributes = 0;
int nb_initial_trans= 0;
id_trans_t id_trans;
trans_id_t trans_id;
vector<int> vtrans_t;
int nb_vtrans = 0;

std::vector<trans_t> tid_code_to_original_array; /**< Foreach virtual
 transaction id, holds the trans_t that contains the tid of the
 original transactions. */

std::vector<BoolMatrix> all_bms; /**< BoolMatrix are used to represent
 the variations between original transactions of each individual
 attribute.  Larger patterns can be built by performing AND operations
 between attribute matrix.
 */

trans_t tid_code_to_original(int code);

/**
 * \brief Fill the boolean matrix \bm from a set of \nb_trans
 * transaction pairs.
 *
 * Boolean variable bm[i, j] is set to one, when the variation
 *   between i and j supports the current pattern.
 * @param bm The boolean matrix to fill.
 * @param transaction pairs of original transactions (records).
 * @param nb_trans number of original transactions (records).
 */
void fill_bool_matrix(BoolMatrix *bm, const id_trans_t &transaction, int nb_trans)
{
  assert(nb_trans == bm->get_size());
  int col, row;
  for(int i = 0; i < transaction.size(); i++){
    /* if transaction in in thransction means t1 < t2 according to the item */
    col = transaction[i].first_;
    row = transaction[i].second_;
    bm->set_value(col, row, 1); /* therefore we set BM[t2][t1] to 1*/
  }
}


void print_grad_transaction(const Transaction &t){
  for(int i = 0; i < t.size(); i++){
    element_print(t[i]);cout<<" " ;
  }
}

 void print_grad_transaction_table(const TransactionTable &tt){
  for(int i = 0; i < tt.size(); i++){
    trans_t t = tid_code_to_original(i);
    cout<<i<<" "<<t.first_<<"x"<<t.second_<<" ("<<tt[i].weight<<") : "; print_grad_transaction(tt[i]);
    cout<<endl;
  }
}

void read_transaction_table_vtrans(TransactionTable *tt, const char *filename){
  ifstream ifs (filename , ifstream::in);
  int nb_items = 0;
  int t1 = 0, t2 = 1;
  ifs.ignore(65536, '\n');  /* skip first line */
  while (ifs.good()){

    string line;
    stringstream ss;
    Transaction t;
    double item;
    ss<<skipws;
    getline(ifs, line);
    ss<<line;
    ss>>item;
    t.reserve(nb_attributes);
    while(ss.good()){
      if(item >= (numeric_limits<int>::max())/1000){
        cerr<<"No value larger than "<<numeric_limits<int>::max()/1000<<" allowed in input file (See. "
            <<__FILE__<<":"<<__LINE__<<")."<<endl;
        abort();
      }
      /* The item*1000 is a simple hack to it also works with float input values, remove if needed. (here and bellow) */
      //t.push_back((int)(item*1000));
    
      t.push_back((int)(item));
      ++nb_items;
      ss>>item;
    }
    if(!ss.fail()){
      //t.push_back((int)(item*1000));
      t.push_back((int)(item));
      ++nb_items;
      //   cout<<"READ "<<item<<endl;
    }
    if(nb_attributes==0)
      nb_attributes = nb_items;

    if(t.size() != 0){
      tt->push_back(t);
      nb_initial_trans++;
    }

  } 
  ifs.close();
}

//AJOUT MIKE SUR LE SEUIL DE GRADUALITE

//Function take 2 parameters : input and type of gradual threshold
// 1 ==> Ecart type
// 2 ==> Coefficient de variation
array<double,10000> GradualThreshold(const TransactionTable &input, int k1, int k2, char* type){
  //Declaration des variables
	array<double,10000> moy;
  array<double,10000> moy_st;
  array<double,10000> sd;
  array<double,10000> cv;
  array<double,10000> st;

  double diff_st[10000];
  double mat_st[10000];
  float aux_sd, v, aux_st, v_diff_sd;
  int q, per;
  // Compute mean of each attribute
  for (int i=0; i<nb_attributes; i++)
  {
    aux_st = 0;
    aux_sd = 0;
    for (int j=0; j<nb_vtrans; j++)
    {     
        // Case of mean
        aux_sd += input[j][i];
        // Case of mean standar deviation
        diff_st[j] = input[j][i];
    }
    //Sort the table // Write the spécific algorithm
    for (int p = 1; p < nb_vtrans; p++)
    {
      q = p-1;
      while (q>=0)
      {
        if (diff_st[q] > diff_st[q+1])
        {
          per = diff_st[q];
          diff_st[q] = diff_st[q+1];
          diff_st[q+1] = per;
          q = q - 1;
        }else{
          q = -1;
        }
      }      
    }
    // Compute Mean
    for (int k = 1; k < nb_vtrans; k++)
    {
      aux_st += (diff_st[k] - diff_st[k-1]);
      mat_st[k-1] = diff_st[k] - diff_st[k-1];
    }
    // Compute moy sd
    moy[i] = aux_sd / (nb_vtrans);
    
    //compute moy st
    moy_st[i] = aux_st / (nb_vtrans - 1);

    //Compute Standard deviation
    v = 0.0;
    v_diff_sd = 0.0;
    // Compute variance écarttype normal
    for(int j=0; j < nb_vtrans; j++){
      v += pow(input[j][i] - moy[i], 2);
      if (j < (nb_vtrans - 1))
      {
        v_diff_sd += pow((mat_st[j]-moy_st[i]),2); 
      }               
    }
      // Ecart type
    v = v/nb_vtrans;
    v_diff_sd = v_diff_sd/(nb_vtrans-1);
    sd[i] = (sqrt(v) * k1) + k2;
    // Différence Ecart type
    st[i] = (sqrt(v_diff_sd) * k1) + k2;

    // Coefficient de variation
		cv[i] = ((sd[i]/moy[i]) * k1 ) + k2;
    //cv[i] = (fabs(sd[i]/moy[i]) * k1 ) + k2;
    //cerr<<"Moy["<<i<<"] = "<<moy[i]<<" # "<<"Moy_st["<<i<<"] = "<<moy_st[i]<<" # "<<"cv["<<i<<"] = "<<cv[i]<<" # "<<"sd["<<i<<"] = "<<sd[i]<<" # "<<"st["<<i<<"] = "<<st[i]<<endl;
  }
  // Return gradual threshold for all attributes
  if (type[0] == 's' && type[1] == 'd')
  {
    return sd;
  }else if(type[0] == 'c' && type[1] == 'v')
  {
    return cv;
  }else if (type[0] == 's' && type[1] == 't')
  {
    return st;
  }
  
  return cv;
    
}

//Memory usage
void process_mem_usage(double& vm_usage, double& resident_set)
{
    vm_usage     = 0.0;
    resident_set = 0.0;

    // the two fields we want
    unsigned long vsize;
    long rss;
    {
        std::string ignore;
        std::ifstream ifs("/proc/self/stat", std::ios_base::in);
        ifs >> ignore >> ignore >> ignore >> ignore >> ignore >> ignore >> ignore >> ignore >> ignore >> ignore
                >> ignore >> ignore >> ignore >> ignore >> ignore >> ignore >> ignore >> ignore >> ignore >> ignore
                >> ignore >> ignore >> vsize >> rss;
    }

    long page_size_kb = sysconf(_SC_PAGE_SIZE) / 1024.0 / 1024.0 / 1024.0; // in case x86-64 is configured to use 2MB pages
    vm_usage = vsize / 1024.0 / 1024.0 / 1024.0;
    resident_set = rss * page_size_kb;
}
//FIN AJOUT MIKE SUR LE SEUIL DE GRADUALITE

int tt_to_grad_items(TransactionTable *output, const TransactionTable &input, array<double,10000> GT){
  output->reserve(input.size()*input.size()-input.size());

  int nb_trans = 0;
  for(int i=0; i < input.size(); i++){
    for(int j = 0; j < input.size(); j++){
      if(i!=j){
        Transaction t;
        t.weight = 1;
        #ifdef TRACK_TIDS
          t.tids.push_back(nb_trans);
        #endif //TRACK_TIDS
        trans_t p;
        p.first_=i;
        p.second_=j;
        tid_code_to_original_array.push_back(p);
        nb_trans++;

        t.reserve(nb_attributes);
        for(int k = 0; k < input[i].size(); k++){
          #ifdef DETECT_NULL_VARIATION
            if((input[i][k] < input[j][k]) && ((input[j][k] - input[i][k]) > GT[k])){
              t.push_back(2*k);
              //cerr<<2*k;
            }
            else if((input[i][k] > input[j][k]) && ((input[i][k] - input[j][k]) > GT[k])){
              t.push_back(2*k+1);
              //cerr<<2*k+1;
            }
            else{
              //t.push_back(2*k);
              //t.push_back(2*k+1);
              //cerr<<2*k;
              //cerr<<2*k+1;
            }
            /*if(input[i][k] < input[j][k]){
              t.push_back(2*k);
            }
            else if(input[i][k] > input[j][k]){
              t.push_back(2*k+1);
            }
            else{
              t.push_back(2*k);
              t.push_back(2*k+1);
              
            }*/
          #else
            if((input[i][k] < input[j][k]) && ((input[j][k] - input[i][k]) > GT[k])){
              t.push_back(2*k);
            }
            else if((input[i][k] > input[j][k]) && ((input[i][k] - input[j][k]) > GT[k])){
              t.push_back(2*k+1);
            }
            else{
              //t.push_back(2*k+(i>j));
            }
            /*if(input[i][k] < input[j][k]){
              t.push_back(2*k);
            }
            else if(input[i][k] > input[j][k]){
              t.push_back(2*k+1);
            }
            else {
            t.push_back(2*k+(i>j));
            }*/

          #endif //DETECT_NULL_VARIATION
        }
        t.limit=t.size();
        output->push_back(t);
      }
    }
  }
  return 0;
}


/**
 * \brief Convert the tid of a vtrans into a pair of original transaction tids.
 * @param code the tid of the vtrans.
 * @return The pair of original transaction tids.
 */
trans_t tid_code_to_original(int code){
  return tid_code_to_original_array[code];
  trans_t t;
  t.first_ = code / (nb_initial_trans-1);
  t.second_ = code % (nb_initial_trans-1);
  if(t.second_ >= t.first_)
    t.second_++;
  return t;
}

void element_print(const element_t element){
  cout<<" "<<(element/2)+1<<(element%2?"-":"+");
}

int support_from_path_lengths(const vector<int> &path_lengths){
  int sup = 0;
  for(int i = 0; i < path_lengths.size(); i++){
    sup = std::max(sup, static_cast<int>(path_lengths[i]));
  }
  return sup;
}

void rec_compute_path_length(int trans, const BoolMatrix &BM,
			     vector<int> *path_length){

  if((*path_length)[trans] != 0)
    return;
  int BMSize = BM.get_size();
  if (!BM.null_row_p(trans)) {

    for(int j = 0; j < BMSize; j++)
      {
  	if (BM.get_value(trans,j))
  	  {

	    //if (BM.checkZero(j)) freMap[trans] = 1;
	    if ((*path_length)[j] == 0)
	      rec_compute_path_length(j,BM, path_length);

	    int current_path_length = (*path_length)[j] + 1;

	    if( current_path_length > (*path_length)[trans]){
	      (*path_length)[trans] = current_path_length;
	    }
	  }
      }
  }
  else{
    (*path_length)[trans] = 1;
  }
}

/* Same as loop_find_longuest_paths() but only computes support value (do not store the paths)*/
int compute_gradual_support(const BoolMatrix &BM, vector<int> *path_length){
  int psize = path_length->size();
  for(int i = 0; i < psize; i++)
    {
      rec_compute_path_length(i,BM, path_length);
    }

  return support_from_path_lengths(*path_length);
}


pair<int,int> retreive_transaction_pairs_count(const TransactionTable &tt, const Occurence &occurences, id_trans_t *transaction_pairs){


  vector<bool> present(nb_vtrans, false);
  int nb_tids = 0;
  int max_tid = 0;
  int nb_pairs = 0;
  for(Occurence::const_iterator it = occurences.begin(); it != occurences.end(); ++it){
    //    original_occurences[i++] = data.tt[*it].original_tid;
    const Transaction &cur = tt[*it];
    for(set_t::const_iterator it2 = cur.tids.begin(); it2 != cur.tids.end(); ++it2){
      trans_t t = tid_code_to_original(*it2);
      if(!present[t.first_]){
	present[t.first_] = true;
	nb_tids++;
	if(t.first_>max_tid)
	  max_tid = t.first_;
      }
      if(!present[t.second_]){
	present[t.second_] = true;
	nb_tids++;
	if(t.second_>max_tid)
	  max_tid = t.second_;
      }
      (*transaction_pairs)[nb_pairs++] = t;
    }
    //cout<<i-1<<" : "<<transaction_pairs[i-1].first<<"x"<<transaction_pairs[i-1].second<<endl;
  }
  return pair<int,int>(nb_tids, max_tid);
}

void detect_short_cycles(const BoolMatrix &bm){
  for (int i = 0; i < bm.get_size(); i++)
    for (int j = 0; j < bm.get_size(); j++)
      if(i != j && bm.get_value(i,j) && bm.get_value(j,i)){
	cerr<<"SHORT CYCLE DETECTED "<<i<<"x"<<j<<endl;
	abort();
      }
}

int membership_oracle(const set_t &base_set, const element_t extension,
		      const membership_data_t &data){

  //  if(data.support[extension]+1 < threshold)
    //return 0;

  set_t s(base_set);
  s.push_back(extension);
  sort(s.begin(), s.end());

  if(s[0]%2==1) /* remove from F sets whose first element is a X- */
      return 0;
  if(base_set.size() == 0)
    nb_vtrans;

  #if 0
for(int i = 0; i < s.size()-1; i++){
    if(s[i]/2 == (s[i+1])/2){
      /* removes sets including X+ X- simultaneously */
      //cout<<"REMOVED : "<<endl;
      //      set_print(s);
      return 0;
    }
  }
#endif
    // if(s.size() == 1)
    //   return 1;


  Occurence occurences;
  set_intersect(&occurences, data.base_set_occurences, data.extension_occurences);
  //  Occurence original_occurences(occurences.size());



  id_trans_t transaction_pairs(data.support[extension]);

  int i=0;

  pair<int,int> nb_max_tids = retreive_transaction_pairs_count(data.tt, occurences, &transaction_pairs);


  // for(int i = 0; i < transaction_pairs.size(); i++){
  //   cout<<transaction_pairs[i].first_<<"x"<<transaction_pairs[i].second_<<endl;
  // }

  BoolMatrix bm(nb_max_tids.first);

  /* Rename tids in the range [0, max_tids] */
  vector<int16_t> back_perms(nb_max_tids.second+1,-1);
  int perm_idx = 0;
  for(id_trans_t::const_iterator it = transaction_pairs.begin(); it != transaction_pairs.end(); ++it){
    int t1, t2;
    if( (t1 = back_perms[it->first_]) == -1){
      t1 = (back_perms[it->first_] = perm_idx++);
    }
    if( (t2 = back_perms[it->second_]) == -1){
      t2 = (back_perms[it->second_] = perm_idx++);
    }

    //    cout<<back_perms[it->first_]<<"->"<<t1<<endl;
    //    cout<<back_perms[it->second_]<<"->"<<t2<<endl;
    bm.set_value(t2,t1, true);
  }


  //sort(transaction_pairs.begin(), transaction_pairs.end());


  //print transaction pairs supporting pattern






    //bm.fill_bool_matrixParaMiner(transaction_pairs, nb_vtrans);
  //  vector<int> path_length(nb_vtrans, 0);

  vector<int> path_length(nb_max_tids.first, 0);
#ifdef DETECT_NULL_VARIATION
  vector<vector<int> > siblings;
  binary_matrix_remove_short_cycles(&bm, &siblings, nb_vtrans);
  int sup = compute_gradual_support_siblings(bm, siblings, &path_length);
#else

#ifndef NDEBUG
  detect_short_cycles(bm);
#endif
  int sup = compute_gradual_support(bm, &path_length);
#endif

  /* Find longuest path (useless)*/
#if 0
  vector<vector< int > > paths(nb_vtrans, vector<int>());
  loop_find_longest_paths(bm, siblings, &path_length, &paths);
  int sup = support_from_path_lengths(path_length);
  // vector<int> path_length2(nb_vtrans, 0);
  // assert( sup == sup2);
#endif



  // cout<<"PATHS"<<endl;
  // for(int i = 0; i < paths.size(); i++){
  //   for(int j = 0; j < paths[i].size(); j++){
  //     cout<<paths[i][j]<<" ";
  //   }
  //   cout<<endl;
  // }
  // getchar();
  // vector<int> freMap(nb_vtrans, -1);
  // //  vector<int> freMap(nb_vtrans, -1);
  // set_t t_weights(nb_vtrans);
  // for(int i = 0; i < siblings.size(); i++){
  //   t_weights[i] = siblings[i].size();
  // }

  // loop_Chk_Freq(bm, freMap, t_weights);
  // int sup = frequentCount(freMap);
  // cout<<"SUP"<<sup<<endl;


  //  int sup = get_longest_path(original_occurences);
  // cout<<"STARTTT"<<endl;
  // set_print(base_set);
  // element_print(extension);
  // cout<<" SUP "<<sup<<endl;
  // set_print_raw(occurences);
  // cout<<"ENDDDDD"<<endl;



 // cout<<"TESTING ("<<sup<<endl;
 // set_print(s);
 // cout<<"DB"<<endl;
 // print_grad_transaction_table(data.tt);
 // cout<<"END"<<endl;

  return sup>=threshold?sup:0;
}


set_t clo(const set_t &set, const closure_data_t &data){
  set_t c(set);
  //return set;
  const Occurence &occs = data.occurences;
  id_trans_t transaction_pairs(occs.size());



  /* Retreive original transaction ids from vtrans ids. */
  int i=0;
  for(Occurence::const_iterator it = occs.begin(); it != occs.end(); ++it){
    transaction_pairs[i++] = tid_code_to_original(data.tt[*it].tids[0]);
  }

  /* Fill a bool matrix: [i, j] is set to one, when the variation
     between i and j supports the current pattern. */
  BoolMatrix bm(nb_vtrans);
  fill_bool_matrix(&bm, transaction_pairs, nb_vtrans);

  bool change = true;

  bool first_positive_flag = false;
  bool discard_next = false;

  for(int i = 0; i <= data.tt.max_element; i++){
    //  for(int i = 0; i < all_bms.size(); i++){
    if(set_member(set, i)){
      if(i%2==0)
	first_positive_flag = true;
    }
    else{
      if(data.support[i] < data.set_support)
	continue;
    /* skip negative items before first positive item */
      if(i%2==1)
	if(!first_positive_flag)
	  continue;

      BoolMatrix bme(all_bms[i]);
      //    restrict_binary_matrix(&bme, longuest_path_nodes);
      bme.bitwise_and(bm);
      if(bme == bm){
	c.push_back(i);
	if(i%2==0)
	  first_positive_flag = true;
      }
    }
  }

  return c;
}


void usage(char *bin_name){
  paraminer_usage(bin_name);
  cerr<<"Problem specific command line arguments:"<<endl;
  cerr<<bin_name<<" [<paraminer options> (See above.)] <dataset> <minsup>"<<endl;
  exit(EXIT_FAILURE);
}


int main(int argc, char **argv){
  double vm_start, rss_start;
  process_mem_usage(vm_start,rss_start);
  cerr<<" MEMORY CONSUMPTION = "<<vm_start<<" RESOURCE = "<<rss_start<<endl;
  time_t start, finish;
  
  //Get time begining
  time(&start);
  auto start_time = std::chrono::high_resolution_clock::now();

  int idx = parse_paraminer_arguments(&argc, argv);
  if(argc-idx != 6){
    usage(argv[0]);
  }
  
  cerr<<endl;
  cerr<<"NAME OF FILE = "<<argv[1]<<endl;
  cerr<<endl;
  cerr<<"MINIMUM SUPPORT = "<<argv[2]<<endl;
  cerr<<endl;
  cerr<<"CONST K1 = "<<argv[3]<<endl;
  cerr<<endl;
  cerr<<"CONST k2 = "<<argv[4]<<endl;
  cerr<<endl;
  cerr<<"THRESHOLD FUNCTION = "<<argv[5]<<endl;
  cerr<<endl;
  
  TransactionTable tmp;
  read_transaction_table_vtrans(&tmp, argv[idx+1]);
  nb_vtrans = tmp.size();
  ELEMENT_RANGE_END = nb_attributes*2;
  
  array<double,10000> GT = GradualThreshold(tmp, atoi(argv[3]), atoi(argv[4]), argv[5]);
  cerr<<"AFTER THRESHOLD"<<endl;
  tt_to_grad_items(&tt, tmp, GT);
  cout<<nb_initial_trans<<endl;
  //  print_transaction_table(tt);

  //  print_grad_transaction_table(tt);
  tt.max_element = ELEMENT_RANGE_END-1;

#ifdef DATABASE_MERGE_TRANS
  merge_identical_transactions(&tt,true);
#endif
  transpose(tt, &ot);

  all_bms.reserve(ELEMENT_RANGE_END);
  for(int i = 0; i < ELEMENT_RANGE_END; i++){
    BoolMatrix bm(nb_vtrans);
    id_trans_t trans;
    for(int j = 0; j < ot[i].size(); j++){
      trans.push_back(tid_code_to_original(ot[i][j]));
    }


   vector<vector<int> > siblings;
   fill_bool_matrix(&bm, trans,nb_vtrans);

  // vector<int> freMap(nb_vtrans, -1);
  // set_t t_weights(nb_vtrans);
  // for(int i = 0; i < siblings.size(); i++){
  //   t_weights[i] = siblings[i].size();
  // }

  //   fill_bool_matrixParaMiner(trans);
  //cout<<endl;
    //     bm.PrintInfo();
    all_bms.push_back(bm);
  }


  float f_threshold = atof(argv[idx+2]);
  if(f_threshold > 1){ //TODO ambiguity when 1 !
    //threshold = std::ceil(f_threshold*(nb_vtrans));
    threshold = std::ceil(f_threshold/(nb_vtrans));
  }
  else{
    threshold = std::ceil(f_threshold * nb_vtrans);
    //threshold = f_threshold;
    //f_threshold = (float)threshold/(nb_vtrans);
  }

  //Finish time
  time(&finish);
  auto end_time = std::chrono::high_resolution_clock::now();
  auto diffTime = end_time - start_time;
  
  //cerr<<"THRESHOLD = "<<f_threshold<<" ["<<threshold<<" / "<<nb_vtrans<<"]"<<endl;
  cerr<<"THRESHOLD = "<<threshold<<" ["<<f_threshold<<" * "<<nb_vtrans<<"]"<<endl;
  set_t empty_set;
  int num_pattern = paraminer(empty_set);
  cout<<num_pattern<<" patterns mined"<<endl;
  cout<<diffTime/std::chrono::milliseconds(1)<<" milliseconds time required"<<endl;
  cerr<<"NUMBER OF PATTERNS MINED = "<<num_pattern<<endl;
  cerr<<"TIME REQUIRED = "<<diffTime/std::chrono::milliseconds(1)<<" MILLISECONDS"<<endl;
  double vm_end, rss_end;
  process_mem_usage(vm_end,rss_end);
  cerr<<" MEMORY CONSUMPTION = "<<vm_end<<" RESOURCE = "<<rss_end<<endl;
  
};
