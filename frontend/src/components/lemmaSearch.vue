<style scoped>
.search-row {
    margin-left: 25px;
    margin-right: 15px;
    display: table;
}

.search-row>div {
    display: table-cell;
    width: 100%;
}

.search-input {
    width: 100%;
}

.btn-search {
    height: fit-content;
}


.list {
    margin-left: 25px;
    overflow-y: scroll;
    max-height: 80vh;
}

.list::-webkit-scrollbar {
    width: 15px;
}

.list::-webkit-scrollbar-corner {
    background: rgba(0, 0, 0, 0);
}

.list::-webkit-scrollbar-thumb {
    background-color: #ccc;
    border-radius: 6px;
    border: 4px solid rgba(0, 0, 0, 0);
    background-clip: content-box;
    min-width: 32px;
    min-height: 32px;
}

.list::-webkit-scrollbar-track {
    background-color: rgba(0, 0, 0, 0);
}


.lemma:hover {
    background-color: #d4d4d4;
}
</style>

<template>
    <div>
        <div class="row my-2 search-row">
            <div>
                <input class="search-input" type="text" placeholder="Search lemma..." maxlength="50" spellcheck="false"
                    v-model="lemmaSearchText" @keydown="searchLemmaKeyDown" />
            </div>
            <button id="lemmas" class="btn btn-info btn-small btn-search ml-2" @click="searchLemmas"
                title="Search for lemmas matching the current name and selection (ctrl+f)">
                Search
            </button>
        </div>
        <ul class="list-group list">
            <template v-for="lemma in lemmaList">
                <li class="list-group-item p-1 my-1 lemma" title="Add this lemma as a hypothesis"
                    @click="addLemma(lemma)">
                    <b>{{ lemma.name }}</b> <br> {{ lemma.form }}
                </li>
            </template>
        </ul>
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
        };
    },
    methods: {
        // Called when the "Search" button is clicked.
        searchLemmas: function () {
            try {
                console.log("Requesting lemmas\n");
                let button = document.getElementById("lemmas");
                button.style.display = "none";

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
                return { handle: l[1][0], name: l[1][1], form: l[1][2] }
            });

            let button = document.getElementById("lemmas");
            button.style.display = "block";
        },

        getLemmaSearchText: function () {
            return this.lemmaSearchText;
        },

        // Callback invoked when user clicks on an entry in the lemma list.
        addLemma: async function (lemma) {
            this.$parent.sendLemma(this.goal, lemma.handle);
        },

        // Callback invoked when the user types in the "search lemmas" input field.
        searchLemmaKeyDown: function (ev) {
            // On [Enter], search for lemmas.
            if (ev.key == "Enter") {
                this.searchLemmas();
            }
        },
    }
};
</script>
