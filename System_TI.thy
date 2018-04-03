theory System_TI
imports Main

begin

type_synonym entity_id = nat

datatype rights = Read|Write|Grant|Create|Take|Store

record cap =  entity :: entity_id
              rights :: "rights set"

record entity =   caps :: "cap set"
                  eValue :: nat

record state =  heap :: "entity_id \<Rightarrow> entity"
                next_id :: entity_id

definition
  all_rights :: "rights set" where
  "all_rights \<equiv> UNIV"

definition
  caps_of :: "state \<Rightarrow> entity_id \<Rightarrow> cap set" where
  "caps_of s sref \<equiv> caps (heap s sref)"

definition
  grant_cap :: "entity_id \<Rightarrow> cap" where
  "grant_cap e \<equiv> \<lparr>entity = e, rights = {Grant}\<rparr>"

definition
  read_cap :: "entity_id \<Rightarrow> cap" where
  "read_cap e\<^sub>x \<equiv> \<lparr>entity = e\<^sub>x, rights = {Read}\<rparr>"

definition
  write_cap :: "entity_id \<Rightarrow> cap" where
  "write_cap e\<^sub>x \<equiv> \<lparr>entity = e\<^sub>x, rights = {Write}\<rparr>"

definition
  take_cap :: "entity_id \<Rightarrow> cap" where
  "take_cap e\<^sub>x \<equiv> \<lparr>entity = e\<^sub>x, rights = {Take}\<rparr>"

definition
  create_cap :: "entity_id \<Rightarrow> cap" where
  "create_cap e\<^sub>x \<equiv> \<lparr>entity = e\<^sub>x, rights = {Create}\<rparr>"

definition
  store_cap :: "entity_id \<Rightarrow> cap" where
  "store_cap e \<equiv> \<lparr>entity = e, rights = {Store}\<rparr>"

definition
  full_cap :: "entity_id \<Rightarrow> cap" where
  "full_cap e \<equiv> \<lparr>entity = e, rights = all_rights \<rparr>"

definition
  lessCap :: "cap \<Rightarrow> cap set \<Rightarrow> bool" where
  "lessCap c C \<equiv> \<exists> d\<in>C. entity c = entity d \<and> rights c \<subseteq> rights d"

definition
  leak :: "state \<Rightarrow> entity_id \<Rightarrow> entity_id \<Rightarrow> bool" where
  "leak s e\<^sub>x e\<^sub>y \<equiv> lessCap (grant_cap e\<^sub>y) (caps_of s e\<^sub>x)"

definition
  connected :: "state \<Rightarrow> entity_id \<Rightarrow> entity_id \<Rightarrow> bool" ("_ \<turnstile> _ \<leftrightarrow> _") where
  "connected s e\<^sub>x e\<^sub>y \<equiv> leak s e\<^sub>x e\<^sub>y \<or> leak s e\<^sub>y e\<^sub>x"


definition
  directly_connected :: "state \<Rightarrow> (entity_id \<times> entity_id) set" where
  "directly_connected s \<equiv> {(e\<^sub>x, e\<^sub>y). leak s e\<^sub>x e\<^sub>y \<or> leak s e\<^sub>y e\<^sub>x}"

definition
  conc_connected :: "state \<Rightarrow> (entity_id \<times> entity_id) set" where
  "conc_connected s \<equiv> (directly_connected s)\<^sup>*"

definition
  in_conc_connected :: "state \<Rightarrow> entity_id \<Rightarrow> entity_id \<Rightarrow> bool"  where
  "in_conc_connected s x y \<equiv> (x,y) \<in> conc_connected s"

definition
  subSys :: "state \<Rightarrow> entity_id \<Rightarrow> entity_id set" where
  "subSys s x \<equiv> {e\<^sub>i, in_conc_connected s x e\<^sub>i}"

definition
  isEntityOf :: "state \<Rightarrow> entity_id \<Rightarrow> bool" where
  "isEntityOf s e \<equiv> e < next_id s"

definition
  value_of :: "state \<Rightarrow> entity_id \<Rightarrow> nat" where
  "value_of s sref \<equiv> eValue(heap s sref)"

