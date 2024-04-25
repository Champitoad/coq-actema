<style scoped>
.search-lemma-bar {
    flex: 3 3 auto;
}

.search-button {
    display: inline-block;
    flex: 0 0 auto;
    height: fit-content;
    margin-left: 15px;
}

.row {
    display: flex;
    align-items: center;
    margin-left: 15px;
    margin-top: 15px;
    margin-right: 0px;
}
</style>

<template>
    <div class="row">
        <vue-simple-suggest class="search-lemma-bar" placeholder="Search lemma..." v-model="lemmaSearchText"
            display-attribute="name" value-attribute="handle" @select="addLemma" :list="lemmaList"
            :filter-by-query="false" :min-length="0" :max-suggestions="15" :preventHide="true" :key="lemmaKey"
            ref="lemmaSearchBar">
            <div slot="suggestion-item" slot-scope="{ suggestion }">
                <div>{{ suggestion.handle }} : {{ suggestion.name }} : {{ suggestion.form }}</div>
            </div>
        </vue-simple-suggest>

        <button id="lemmas" class="btn btn-info search-button" @click="searchLemmas"
            title="Search for lemmas matching the current name and selection (ctrl+f)">
            Search
        </button>
    </div>
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
        searchLemmas: function () {
            try {
                console.log("Requesting lemmas\n");

                let pattern = this.getLemmaSearchText();
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
            setTimeout(() => {
                this.$refs.lemmaSearchBar.input.focus();
            }, 0);
        },

        // Callback invoked when we click on an entry in the lemma dropdown (list).
        addLemma: async function (lemma) {
            this.$parent.sendLemma(this.goal, lemma.handle);
        },
    }
};
</script>
