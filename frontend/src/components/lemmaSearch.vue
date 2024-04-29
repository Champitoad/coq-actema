<style scoped>
.list {
    margin-left: 25px;
}

.search-lemma-input {
    display: inline-block;
}

.btn-search {
    display: inline-block;
    margin-left: auto;
    height: fit-content;
}

.lemma {
    font-size: 15;
}

.lemma:hover {
    background-color: #d4d4d4;
}
</style>

<template>
    <ul class="list-group list">
        <li class="row my-2">
            <input class="search-lemma-input" type="text" placeholder="Search lemma..." maxlength="50"
                v-model="lemmaSearchText" />
            <button id="lemmas" class="btn btn-info btn-small btn-search ml-2" @click="searchLemmas"
                title="Search for lemmas matching the current name and selection (ctrl+f)">
                Search
            </button>
        </li>
        <template v-for="lemma in lemmaList">
            <li class="row p-1 my-1 lemma" @onclick="addLemma(lemma)">
                <b>{{ lemma.name }}</b>{{ lemma.form }}
            </li>
        </template>
    </ul>
</template>

<script>
import _ from "lodash";

import Vue from 'vue';
import VueSweetalert2 from 'vue-sweetalert2';
import 'sweetalert2/dist/sweetalert2.min.css';

import VueSimpleSuggest from 'vue-simple-suggest'
import 'vue-simple-suggest/dist/styles.css' // Optional CSS

Vue.use(VueSweetalert2);

export default {
    props: ["goal", "context", "vars", "selectMode", "displayMode"],
    components: {
        VueSimpleSuggest
    },
    data: function () {
        return {
            lemmaList: [],
            lemmaSearchText: "",
            // A variable used to force a re-render of the lemma list when needed.
            // This is known as the key-changing technique. For more information see :
            // https://michaelnthiessen.com/force-re-render
            lemmaKey: 0,
        };
    },
    methods: {
        // Called when the "Search" button is clicked.
        searchLemmas: async function () {
            try {
                console.log("Requesting lemmas\n");

                let pattern = this.lemmaSearchText;
                let selection = this.$parent.getActiveSelection();
                let proofState = this.$parent.getProofState();
                let msg = proofState.lemmareqb(selection, pattern);

                window.ipcRenderer.send('request_lemmas', msg);
            } catch (e) {
                this.$parent.showErrorMessage(e);
                window.ipcRenderer.send('error', this.$parent.errorMsg);
            }
        },

        updateLemmaList: function () {
            let lemmas = Object.entries(this.$parent.proofState.getlemmas());

            this.lemmaList = _.map(lemmas, l => {
                //console.log(l);
                return { handle: l[1][0], name: l[1][1], form: l[1][2] }
            });

            // Force a re-render of the lemma list.
            this.lemmaKey += 1;
        },

        getLemmaSearchText: function () {
            return this.lemmaSearchText;
        },

        focusLemmaSearchBar: function () {
            // For some reason using "setTimeout" is necessary here.
            // For somewhat of an explanation read :
            // https://bobbyhadz.com/blog/focus-not-working-in-javascript
            //setTimeout(() => {
            //    this.$refs.lemmaSearchBar.input.focus();
            //}, 0);
        },

        // Callback invoked when we click on an entry in the lemma dropdown (list).
        addLemma: async function (lemma) {
            this.$parent.sendLemma(this.goal, lemma.handle);
        },
    }
};
</script>
